//! Cold, exact declaration of a fixed generator machine.
//!
//! This module is deliberately not wired into the legacy `GeometricFieldSpec`.  It is the
//! packet-3/reference boundary: the machine has a fixed population of situated screws and
//! directed contacts, while source and response lengths remain external costs.  All geometry is
//! carried by the existing exact screw, affine, winding and helical-interaction owners.

use holonic_engine::{
    exact_linear::{ExactLinearError, ExactRatMatrix},
    holonic_interaction::{
        Clock, InteractionRefusal,
        helical::{HelicalPairInteraction, HelicalRefusal, PairUnits},
    },
    inertia::{SymmetricForm, inertia},
};
use num_traits::Signed;
use relational_geometry::{
    AffineMap3, PairFiniteMotion, Rat, RatMat3, RatVec3, RationalPhase, ScrewError, ScrewGenerator,
    ScrewPair, SiteFactor, SituatedScrew, triangle_holonomy,
};
use serde::{Deserialize, Deserializer, Serialize, de::Error as DeError};
use thiserror::Error;

/// Wire/schema version for the bounded machine declaration.
pub const GENERATOR_MACHINE_SCHEMA: &str = "org.holonics.hna.generator-machine.v1";
pub const GENERATOR_MACHINE_VERSION: u32 = 1;

/// The first machine's resident current chart: three complex channels, represented as six exact
/// real coordinates.  The imaginary directions remain internal current modes; only `real` enters
/// the spatial chart below.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplexCurrent3 {
    pub real: RatVec3,
    pub imaginary: RatVec3,
}

/// An induced action on the real coefficient chart of `ComplexCurrent3`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CurrentAffineMap {
    pub linear: RatMat3,
    /// The bias is real.  It is not applied to the imaginary current directions.
    pub bias: RatVec3,
}

impl CurrentAffineMap {
    pub fn apply(&self, current: &ComplexCurrent3) -> ComplexCurrent3 {
        ComplexCurrent3 {
            real: self.linear.apply(&current.real).add(&self.bias),
            imaginary: self.linear.apply(&current.imaginary),
        }
    }

    /// The affine offset residual at `q = 0`, `κ_r(U0) − Tκ_s(0)`.  The full chart realization
    /// also requires equality of the linear coefficients; [`Self::realizes`] checks both.
    pub fn spatial_residual(
        &self,
        source_initial: &RatVec3,
        receiver_initial: &RatVec3,
        transport: &AffineMap3,
    ) -> RatVec3 {
        receiver_initial
            .add(&self.bias)
            .subtract(&transport.apply(source_initial))
    }

    pub fn realizes(
        &self,
        source_initial: &RatVec3,
        receiver_initial: &RatVec3,
        transport: &AffineMap3,
    ) -> bool {
        self.linear == transport.linear
            && self.spatial_residual(source_initial, receiver_initial, transport) == RatVec3::zero()
    }
}

/// Serializable exact phase/lift declaration.  `origin_exponent` is a source/receiver binding
/// coordinate; it is not silently converted into a sample or output-token index.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PhaseSpec {
    pub parameter: Rat,
    pub extra_turns: i64,
    pub origin_exponent: i64,
    pub step: AffineMap3,
    /// A period is a claim about the full supplied affine action.  `None` means that no closure
    /// witness was supplied; it is neither a closure proof nor a nonclosure proof.
    pub period: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClockSpec {
    pub lineage: String,
    pub duration: Rat,
    pub unit: String,
}

impl ClockSpec {
    fn compile(&self) -> Result<Clock, MachineError> {
        if self.lineage.is_empty() || self.unit.is_empty() {
            return Err(MachineError::EmptyLabel {
                what: "clock lineage/unit",
            });
        }
        Ok(Clock::declared(
            self.lineage.clone(),
            self.duration.clone(),
            self.unit.clone(),
        )?)
    }
}

/// Site identity, situated screw and participating source/receiver roles.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSiteSpec {
    pub id: String,
    pub angular: RatVec3,
    pub advance: RatVec3,
    pub initial: RatVec3,
    pub phase: PhaseSpec,
    pub clock: ClockSpec,
    pub source: bool,
    pub receiver: bool,
    /// The actual supplied 2×2 transfer material.  No factor is inferred when this is absent.
    pub material: Option<[[Rat; 2]; 2]>,
}

/// A directed source-to-receiver machine arc.  `source_to_receiver` is a supplied proper rigid
/// action.  `rate_port` is the explicit `C` from the two 6-real-coordinate complex site charts
/// to pair rates `[receiver-rate, source-rate]`, with ambient columns ordered
/// `[receiver complex-3, source complex-3]`, each complex block interleaved as real/imaginary
/// channels.  `parameter_units` use that same receiver/source order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GeneratorPairArcSpec {
    pub id: String,
    pub source: String,
    pub receiver: String,
    pub source_to_receiver: AffineMap3,
    pub rate_port: ExactRatMatrix,
    pub response: SymmetricForm,
    pub weight: Rat,
    pub clock: ClockSpec,
    pub parameter_units: [String; 2],
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GeneratorPairArcSpecWire {
    id: String,
    source: String,
    receiver: String,
    source_to_receiver: AffineMap3,
    rate_port: ExactRatMatrix,
    response: SymmetricForm,
    weight: Rat,
    clock: ClockSpec,
    parameter_units: [String; 2],
}

impl<'de> Deserialize<'de> for GeneratorPairArcSpec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = GeneratorPairArcSpecWire::deserialize(deserializer)?;
        let arc = Self {
            id: wire.id,
            source: wire.source,
            receiver: wire.receiver,
            source_to_receiver: wire.source_to_receiver,
            rate_port: wire.rate_port,
            response: wire.response,
            weight: wire.weight,
            clock: wire.clock,
            parameter_units: wire.parameter_units,
        };
        validate_arc_local(&arc).map_err(|error| D::Error::custom(error.to_string()))?;
        Ok(arc)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CellEdgeSpec {
    /// An admitted machine arc.  The edge endpoints and transport are derived from this arc;
    /// they cannot be authored independently of the pair declaration.
    pub arc: String,
    /// Traverse the admitted arc backwards, using its exact affine inverse.
    pub reversed: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OrientedCellSpec {
    pub id: String,
    pub edges: [CellEdgeSpec; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MachineUnitsSpec {
    /// Common coordinate unit in this unscaled Euclidean spatial chart. R is dimensionless.
    pub spatial: [String; 3],
    /// Interleaved Re0, Im0, Re1, Im1, Re2, Im2. The present κ=p+Re(q) and the same
    /// rotation on both halves require the common spatial coordinate unit in every slot.
    pub current: [String; 6],
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GeneratorMachineSpec {
    schema: String,
    version: u32,
    frame: String,
    units: MachineUnitsSpec,
    sites: Vec<GeneratorSiteSpec>,
    arcs: Vec<GeneratorPairArcSpec>,
    cells: Vec<OrientedCellSpec>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GeneratorMachineSpecWire {
    schema: String,
    version: u32,
    frame: String,
    units: MachineUnitsSpec,
    sites: Vec<GeneratorSiteSpec>,
    arcs: Vec<GeneratorPairArcSpec>,
    cells: Vec<OrientedCellSpec>,
}

impl Serialize for GeneratorMachineSpec {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        #[derive(Serialize)]
        struct Wire<'a> {
            schema: &'a str,
            version: u32,
            frame: &'a str,
            units: &'a MachineUnitsSpec,
            sites: &'a [GeneratorSiteSpec],
            arcs: &'a [GeneratorPairArcSpec],
            cells: &'a [OrientedCellSpec],
        }
        Wire {
            schema: &self.schema,
            version: self.version,
            frame: &self.frame,
            units: &self.units,
            sites: &self.sites,
            arcs: &self.arcs,
            cells: &self.cells,
        }
        .serialize(serializer)
    }
}

impl<'de> Deserialize<'de> for GeneratorMachineSpec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = GeneratorMachineSpecWire::deserialize(deserializer)?;
        if wire.schema != GENERATOR_MACHINE_SCHEMA {
            return Err(D::Error::custom("generator machine schema"));
        }
        if wire.version != GENERATOR_MACHINE_VERSION {
            return Err(D::Error::custom("generator machine version"));
        }
        Self::declare(wire.frame, wire.units, wire.sites, wire.arcs, wire.cells)
            .map_err(|error| D::Error::custom(error.to_string()))
    }
}

impl GeneratorMachineSpec {
    pub fn declare(
        frame: impl Into<String>,
        units: MachineUnitsSpec,
        sites: Vec<GeneratorSiteSpec>,
        arcs: Vec<GeneratorPairArcSpec>,
        cells: Vec<OrientedCellSpec>,
    ) -> Result<Self, MachineError> {
        let frame = frame.into();
        if frame.is_empty() {
            return Err(MachineError::EmptyLabel {
                what: "machine frame",
            });
        }
        validate_units(&units)?;
        if sites.is_empty() {
            return Err(MachineError::EmptyLabel {
                what: "machine site population",
            });
        }
        let _work = sites
            .len()
            .checked_mul(6)
            .and_then(|value| value.checked_add(arcs.len().checked_mul(12)?))
            .and_then(|value| value.checked_add(cells.len().checked_mul(3)?))
            .ok_or(MachineError::WorkOverflow {
                what: "machine declaration",
            })?;
        let mut ids = std::collections::BTreeSet::new();
        for site in &sites {
            validate_site(site)?;
            if !ids.insert(site.id.clone()) {
                return Err(MachineError::DuplicateId(site.id.clone()));
            }
        }
        let mut arc_ids = std::collections::BTreeSet::new();
        for arc in &arcs {
            validate_arc_local(arc)?;
            if !arc_ids.insert(arc.id.clone()) {
                return Err(MachineError::DuplicateId(arc.id.clone()));
            }
            if !ids.contains(&arc.source) {
                return Err(MachineError::UnknownSite(arc.source.clone()));
            }
            if !ids.contains(&arc.receiver) {
                return Err(MachineError::UnknownSite(arc.receiver.clone()));
            }
            if arc.source == arc.receiver {
                return Err(MachineError::SelfArc(arc.id.clone()));
            }
        }
        let mut cell_ids = std::collections::BTreeSet::new();
        for cell in &cells {
            if cell.id.is_empty() {
                return Err(MachineError::EmptyLabel { what: "cell id" });
            }
            if !cell_ids.insert(cell.id.clone()) {
                return Err(MachineError::DuplicateId(cell.id.clone()));
            }
            validate_cell_edges(&cell.edges, &arcs)?;
        }
        Ok(Self {
            schema: GENERATOR_MACHINE_SCHEMA.to_owned(),
            version: GENERATOR_MACHINE_VERSION,
            frame,
            units,
            sites,
            arcs,
            cells,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }
    pub fn version(&self) -> u32 {
        self.version
    }
    pub fn frame(&self) -> &str {
        &self.frame
    }
    pub fn units(&self) -> &MachineUnitsSpec {
        &self.units
    }
    pub fn sites(&self) -> &[GeneratorSiteSpec] {
        &self.sites
    }
    pub fn arcs(&self) -> &[GeneratorPairArcSpec] {
        &self.arcs
    }
    pub fn cells(&self) -> &[OrientedCellSpec] {
        &self.cells
    }

    pub fn compile(&self) -> Result<CompiledGeneratorMachine, MachineError> {
        let mut site_index = std::collections::BTreeMap::new();
        let mut compiled_sites = Vec::with_capacity(self.sites.len());
        for (index, site) in self.sites.iter().enumerate() {
            site_index.insert(site.id.clone(), index);
            compiled_sites.push(CompiledGeneratorSite::compile(site, &self.frame)?);
        }
        let mut compiled_arcs = Vec::with_capacity(self.arcs.len());
        for arc in &self.arcs {
            let source_index = *site_index
                .get(&arc.source)
                .ok_or_else(|| MachineError::UnknownSite(arc.source.clone()))?;
            let receiver_index = *site_index
                .get(&arc.receiver)
                .ok_or_else(|| MachineError::UnknownSite(arc.receiver.clone()))?;
            let source = &compiled_sites[source_index];
            let receiver = &compiled_sites[receiver_index];
            let current_action = CurrentAffineMap::between(
                source.screw.initial(),
                receiver.screw.initial(),
                &arc.source_to_receiver,
            );
            if !current_action.realizes(
                source.screw.initial(),
                receiver.screw.initial(),
                &arc.source_to_receiver,
            ) {
                return Err(MachineError::ChartResidual(arc.id.clone()));
            }
            // The pair is received in the receiver frame: first is the receiver, second is the
            // source carried through the admitted source→receiver action.  Thus its separation is
            // `x_receiver − T x_source`, and its pair-rate columns are
            // `[receiver-rate, source-rate]` as declared by the arc.
            let transported_source = source.screw.transported(&arc.source_to_receiver)?;
            let pair = ScrewPair::new(receiver.screw.clone(), transported_source);
            let clock = arc.clock.compile()?;
            let interaction = HelicalPairInteraction::declared_with_blocks(
                format!("{}|{}", self.frame, arc.id),
                pair,
                arc.rate_port.clone(),
                6,
                6,
                arc.response.clone(),
                arc.weight.clone(),
                clock,
                PairUnits::declared(self.frame.clone(), arc.parameter_units.clone()),
            )?;
            compiled_arcs.push(CompiledGeneratorPairArc {
                id: arc.id.clone(),
                source: arc.source.clone(),
                receiver: arc.receiver.clone(),
                source_index,
                receiver_index,
                source_to_receiver: arc.source_to_receiver.clone(),
                current_action,
                interaction,
            });
        }
        let mut compiled_cells = Vec::with_capacity(self.cells.len());
        let arc_by_id: std::collections::BTreeMap<_, _> = compiled_arcs
            .iter()
            .map(|arc| (arc.id.clone(), arc))
            .collect();
        for cell in &self.cells {
            let edges = cell
                .edges
                .iter()
                .map(|edge| resolve_cell_edge(edge, &arc_by_id))
                .collect::<Result<Vec<_>, _>>()?;
            let edges: [CompiledCellEdge; 3] =
                edges.try_into().map_err(|_| MachineError::WorkOverflow {
                    what: "a triangular cell edge array",
                })?;
            let holonomy = triangle_holonomy(
                &edges[0].transport,
                &edges[1].transport,
                &edges[2].transport,
            );
            compiled_cells.push(CompiledOrientedCell {
                id: cell.id.clone(),
                edges,
                holonomy,
            });
        }
        let supplied_factors = compiled_sites
            .iter()
            .filter_map(|site| site.factor.clone())
            .collect::<Vec<_>>();
        let trace_machine = (supplied_factors.len() == compiled_sites.len())
            .then(|| relational_geometry::Machine::new(supplied_factors));
        Ok(CompiledGeneratorMachine {
            frame: self.frame.clone(),
            units: self.units.clone(),
            sites: compiled_sites,
            arcs: compiled_arcs,
            cells: compiled_cells,
            trace_machine,
        })
    }
}

impl CurrentAffineMap {
    pub fn between(source: &RatVec3, receiver: &RatVec3, transport: &AffineMap3) -> Self {
        Self {
            linear: transport.linear.clone(),
            bias: transport
                .linear
                .apply(source)
                .add(&transport.translation)
                .subtract(receiver),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CompiledGeneratorSite {
    id: String,
    screw: SituatedScrew,
    phase: RationalPhase,
    phase_origin_exponent: i64,
    phase_action: AffineMap3,
    phase_correspondence: PhaseCorrespondence,
    current_action: CurrentAffineMap,
    clock: Clock,
    source: bool,
    receiver: bool,
    material: Option<[[Rat; 2]; 2]>,
    factor: Option<SiteFactor>,
    closure: Option<usize>,
}

impl CompiledGeneratorSite {
    fn compile(site: &GeneratorSiteSpec, _frame: &str) -> Result<Self, MachineError> {
        if !site.phase.step.linear.is_special_orthogonal() {
            return Err(MachineError::NotProperRigid {
                what: format!("site {} phase action", site.id),
            });
        }
        let closure = validate_closure(&site.phase.step, site.phase.period)?;
        let phase = RationalPhase::new(site.phase.parameter.clone(), site.phase.extra_turns);
        let phase_correspondence = if PairFiniteMotion::with_phase(
            site.phase.step.clone(),
            AffineMap3::identity(),
            phase.clone(),
        )
        .is_ok()
        {
            PhaseCorrespondence::SupportedCayleyFiniteMap {
                generator_clock_residual:
                    "finite phase map is not a witness for screw-generator/clock evolution"
                        .to_owned(),
            }
        } else {
            PhaseCorrespondence::SuppliedRigidAction {
                finite_map_residual:
                    "the supplied finite action has no supported Cayley-z phase witness".to_owned(),
                generator_clock_residual:
                    "no screw-generator/clock relation is inferred from a finite action".to_owned(),
            }
        };
        let screw = SituatedScrew::new(
            ScrewGenerator::new(site.angular.clone(), site.advance.clone()),
            site.initial.clone(),
        );
        let current_action =
            CurrentAffineMap::between(&site.initial, &site.initial, &site.phase.step);
        let factor = site.material.as_ref().map(site_factor);
        Ok(Self {
            id: site.id.clone(),
            screw,
            phase,
            phase_origin_exponent: site.phase.origin_exponent,
            phase_action: site.phase.step.clone(),
            phase_correspondence,
            current_action,
            clock: site.clock.compile()?,
            source: site.source,
            receiver: site.receiver,
            material: site.material.clone(),
            factor,
            closure,
        })
    }

    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn screw(&self) -> &SituatedScrew {
        &self.screw
    }
    pub fn phase(&self) -> &RationalPhase {
        &self.phase
    }
    pub fn phase_origin_exponent(&self) -> i64 {
        self.phase_origin_exponent
    }
    pub fn phase_action(&self) -> &AffineMap3 {
        &self.phase_action
    }
    pub fn phase_correspondence(&self) -> &PhaseCorrespondence {
        &self.phase_correspondence
    }
    pub fn current_action(&self) -> &CurrentAffineMap {
        &self.current_action
    }
    pub fn clock(&self) -> &Clock {
        &self.clock
    }
    pub fn is_source(&self) -> bool {
        self.source
    }
    pub fn is_receiver(&self) -> bool {
        self.receiver
    }
    pub fn material(&self) -> Option<&[[Rat; 2]; 2]> {
        self.material.as_ref()
    }
    pub fn factor(&self) -> Option<&SiteFactor> {
        self.factor.as_ref()
    }
    pub fn closure(&self) -> Option<usize> {
        self.closure
    }
}

/// The exact scope of the phase/action bridge.  Neither arm certifies a relation between the
/// finite action and the supplied screw generator or physical clock.  A supplied proper rigid
/// action remains fully usable when it has no such witness.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PhaseCorrespondence {
    SupportedCayleyFiniteMap {
        generator_clock_residual: String,
    },
    SuppliedRigidAction {
        finite_map_residual: String,
        generator_clock_residual: String,
    },
}

#[derive(Clone, Debug)]
pub struct CompiledGeneratorPairArc {
    id: String,
    source: String,
    receiver: String,
    source_index: usize,
    receiver_index: usize,
    source_to_receiver: AffineMap3,
    current_action: CurrentAffineMap,
    interaction: HelicalPairInteraction,
}

impl CompiledGeneratorPairArc {
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn source(&self) -> &str {
        &self.source
    }
    pub fn receiver(&self) -> &str {
        &self.receiver
    }
    pub fn source_index(&self) -> usize {
        self.source_index
    }
    pub fn receiver_index(&self) -> usize {
        self.receiver_index
    }
    pub fn source_to_receiver(&self) -> &AffineMap3 {
        &self.source_to_receiver
    }
    pub fn current_action(&self) -> &CurrentAffineMap {
        &self.current_action
    }
    pub fn interaction(&self) -> &HelicalPairInteraction {
        &self.interaction
    }
}

#[derive(Clone, Debug)]
pub struct CompiledCellEdge {
    arc: String,
    reversed: bool,
    source: String,
    receiver: String,
    transport: AffineMap3,
}

impl CompiledCellEdge {
    pub fn arc(&self) -> &str {
        &self.arc
    }
    pub fn reversed(&self) -> bool {
        self.reversed
    }
    pub fn source(&self) -> &str {
        &self.source
    }
    pub fn receiver(&self) -> &str {
        &self.receiver
    }
    pub fn transport(&self) -> &AffineMap3 {
        &self.transport
    }
}

#[derive(Clone, Debug)]
pub struct CompiledOrientedCell {
    id: String,
    edges: [CompiledCellEdge; 3],
    holonomy: AffineMap3,
}

impl CompiledOrientedCell {
    pub fn id(&self) -> &str {
        &self.id
    }
    pub fn edges(&self) -> &[CompiledCellEdge; 3] {
        &self.edges
    }
    pub fn holonomy(&self) -> &AffineMap3 {
        &self.holonomy
    }
}

#[derive(Clone, Debug)]
pub struct CompiledGeneratorMachine {
    frame: String,
    units: MachineUnitsSpec,
    sites: Vec<CompiledGeneratorSite>,
    arcs: Vec<CompiledGeneratorPairArc>,
    cells: Vec<CompiledOrientedCell>,
    trace_machine: Option<relational_geometry::Machine>,
}

impl CompiledGeneratorMachine {
    pub fn frame(&self) -> &str {
        &self.frame
    }
    pub fn units(&self) -> &MachineUnitsSpec {
        &self.units
    }
    pub fn sites(&self) -> &[CompiledGeneratorSite] {
        &self.sites
    }
    pub fn arcs(&self) -> &[CompiledGeneratorPairArc] {
        &self.arcs
    }
    pub fn cells(&self) -> &[CompiledOrientedCell] {
        &self.cells
    }
    pub fn trace_machine(&self) -> Option<&relational_geometry::Machine> {
        self.trace_machine.as_ref()
    }
    pub fn source_sites(&self) -> impl Iterator<Item = &CompiledGeneratorSite> {
        self.sites.iter().filter(|site| site.source)
    }
    pub fn receiver_sites(&self) -> impl Iterator<Item = &CompiledGeneratorSite> {
        self.sites.iter().filter(|site| site.receiver)
    }
}

#[derive(Debug, Error)]
pub enum MachineError {
    #[error("{what} is empty")]
    EmptyLabel { what: &'static str },
    #[error("duplicate machine identity {0}")]
    DuplicateId(String),
    #[error("unknown site identity {0}")]
    UnknownSite(String),
    #[error("arc {0} has identical source and receiver")]
    SelfArc(String),
    #[error("{what} is not a proper rigid action")]
    NotProperRigid { what: String },
    #[error("{what} is not strictly positive")]
    NonPositive { what: &'static str },
    #[error("the unscaled Euclidean spatial/current chart requires a common coordinate unit")]
    IncompatibleUnits,
    #[error("the response has extent {0}; pair contact requires 3")]
    ResponseExtent(usize),
    #[error("the rate port must be exactly 2×12 for the two complex-3 site charts")]
    RatePortShape,
    #[error("declared work for {what} overflows")]
    WorkOverflow { what: &'static str },
    #[error("phase action does not close at declared period {period}")]
    NotClosed { period: usize },
    #[error("cell edge {edge} has source {from_site} but previous edge ends at {expected}")]
    CellWord {
        edge: usize,
        from_site: String,
        expected: String,
    },
    #[error("cell references absent arc {0}")]
    UnknownArc(String),
    #[error("cell repeats admitted arc {0}")]
    RepeatedCellArc(String),
    #[error("cell does not have three distinct vertices")]
    DegenerateCell,
    #[error(
        "the response is not positive semidefinite: signature ({positive}, {nullity}, {negative})"
    )]
    ResponseNotPositiveSemidefinite {
        positive: usize,
        negative: usize,
        nullity: usize,
    },
    #[error("the exact matrix carrier has rows {rows}, columns {columns}, and {entries} entries")]
    MalformedMatrixCarrier {
        rows: usize,
        columns: usize,
        entries: usize,
    },
    #[error("current chart residual remains on arc {0}")]
    ChartResidual(String),
    #[error(transparent)]
    Clock(#[from] InteractionRefusal),
    #[error(transparent)]
    Helical(#[from] HelicalRefusal),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Screw(#[from] ScrewError),
    #[error(transparent)]
    Winding(#[from] relational_geometry::winding::WindingError),
}

fn validate_units(units: &MachineUnitsSpec) -> Result<(), MachineError> {
    if units.spatial.iter().any(String::is_empty) || units.current.iter().any(String::is_empty) {
        return Err(MachineError::EmptyLabel {
            what: "machine unit",
        });
    }
    if units
        .spatial
        .iter()
        .chain(&units.current)
        .any(|u| u != &units.spatial[0])
    {
        return Err(MachineError::IncompatibleUnits);
    }
    Ok(())
}

fn validate_arc_local(arc: &GeneratorPairArcSpec) -> Result<(), MachineError> {
    if arc.id.is_empty() {
        return Err(MachineError::EmptyLabel { what: "arc id" });
    }
    if arc.source.is_empty() {
        return Err(MachineError::EmptyLabel { what: "arc source" });
    }
    if arc.receiver.is_empty() {
        return Err(MachineError::EmptyLabel {
            what: "arc receiver",
        });
    }
    if !arc.source_to_receiver.linear.is_special_orthogonal() {
        return Err(MachineError::NotProperRigid {
            what: format!("arc {}", arc.id),
        });
    }
    if arc.parameter_units.iter().any(String::is_empty) {
        return Err(MachineError::EmptyLabel {
            what: "pair parameter unit",
        });
    }
    arc.clock.compile()?;
    validate_rate_port(&arc.rate_port)?;
    if arc.response.extent() != 3 {
        return Err(MachineError::ResponseExtent(arc.response.extent()));
    }
    let response_signature = inertia(&arc.response);
    if !response_signature.is_positive_semidefinite() {
        return Err(MachineError::ResponseNotPositiveSemidefinite {
            positive: response_signature.positive,
            negative: response_signature.negative,
            nullity: response_signature.zero,
        });
    }
    if !arc.weight.is_positive() {
        return Err(MachineError::NonPositive { what: "arc weight" });
    }
    Ok(())
}

fn validate_site(site: &GeneratorSiteSpec) -> Result<(), MachineError> {
    if site.id.is_empty() {
        return Err(MachineError::EmptyLabel { what: "site id" });
    }
    if site.clock.lineage.is_empty() || site.clock.unit.is_empty() {
        return Err(MachineError::EmptyLabel {
            what: "site clock lineage/unit",
        });
    }
    if !site.phase.step.linear.is_special_orthogonal() {
        return Err(MachineError::NotProperRigid {
            what: format!("site {} phase action", site.id),
        });
    }
    site.clock.compile()?;
    validate_closure(&site.phase.step, site.phase.period)?;
    Ok(())
}

fn validate_rate_port(port: &ExactRatMatrix) -> Result<(), MachineError> {
    if port.rows().checked_mul(port.columns()) != Some(port.entries().len()) {
        return Err(MachineError::MalformedMatrixCarrier {
            rows: port.rows(),
            columns: port.columns(),
            entries: port.entries().len(),
        });
    }
    if port.rows() != 2 || port.columns() != 12 {
        return Err(MachineError::RatePortShape);
    }
    Ok(())
}

fn validate_cell_edges(
    edges: &[CellEdgeSpec; 3],
    arcs: &[GeneratorPairArcSpec],
) -> Result<(), MachineError> {
    let arc_by_id: std::collections::BTreeMap<_, _> =
        arcs.iter().map(|arc| (arc.id.as_str(), arc)).collect();
    let mut used = std::collections::BTreeSet::new();
    let mut endpoints = Vec::new();
    for edge in edges {
        let arc = arc_by_id
            .get(edge.arc.as_str())
            .ok_or_else(|| MachineError::UnknownArc(edge.arc.clone()))?;
        if !used.insert(edge.arc.clone()) {
            return Err(MachineError::RepeatedCellArc(edge.arc.clone()));
        }
        let (source, receiver) = if edge.reversed {
            (arc.receiver.clone(), arc.source.clone())
        } else {
            (arc.source.clone(), arc.receiver.clone())
        };
        if edge.reversed && arc.source_to_receiver.inverse().is_none() {
            return Err(MachineError::NotProperRigid {
                what: format!("reverse of cell arc {}", edge.arc),
            });
        }
        endpoints.push((source, receiver));
    }
    for index in 0..3 {
        let next = (index + 1) % 3;
        if endpoints[index].1 != endpoints[next].0 {
            return Err(MachineError::CellWord {
                edge: next,
                from_site: endpoints[next].0.clone(),
                expected: endpoints[index].1.clone(),
            });
        }
    }
    let vertices = [
        endpoints[0].0.clone(),
        endpoints[0].1.clone(),
        endpoints[1].1.clone(),
    ];
    if vertices[0] == vertices[1] || vertices[1] == vertices[2] || vertices[2] == vertices[0] {
        return Err(MachineError::DegenerateCell);
    }
    Ok(())
}

fn resolve_cell_edge(
    edge: &CellEdgeSpec,
    arcs: &std::collections::BTreeMap<String, &CompiledGeneratorPairArc>,
) -> Result<CompiledCellEdge, MachineError> {
    let arc = arcs
        .get(&edge.arc)
        .ok_or_else(|| MachineError::UnknownArc(edge.arc.clone()))?;
    if edge.reversed {
        let transport =
            arc.source_to_receiver
                .inverse()
                .ok_or_else(|| MachineError::NotProperRigid {
                    what: format!("reverse of cell arc {}", edge.arc),
                })?;
        Ok(CompiledCellEdge {
            arc: edge.arc.clone(),
            reversed: true,
            source: arc.receiver.clone(),
            receiver: arc.source.clone(),
            transport,
        })
    } else {
        Ok(CompiledCellEdge {
            arc: edge.arc.clone(),
            reversed: false,
            source: arc.source.clone(),
            receiver: arc.receiver.clone(),
            transport: arc.source_to_receiver.clone(),
        })
    }
}

fn validate_closure(
    action: &AffineMap3,
    period: Option<usize>,
) -> Result<Option<usize>, MachineError> {
    let Some(period) = period else {
        return Ok(None);
    };
    if period == 0 || affine_power(action, period) != AffineMap3::identity() {
        return Err(MachineError::NotClosed { period });
    }
    Ok(Some(period))
}

fn affine_power(action: &AffineMap3, mut exponent: usize) -> AffineMap3 {
    let mut result = AffineMap3::identity();
    let mut base = action.clone();
    while exponent > 0 {
        if exponent % 2 == 1 {
            result = result.followed_by(&base);
        }
        exponent /= 2;
        if exponent > 0 {
            base = base.followed_by(&base);
        }
    }
    result
}

fn site_factor(material: &[[Rat; 2]; 2]) -> SiteFactor {
    let trace = &material[0][0] + &material[1][1];
    let determinant = &material[0][0] * &material[1][1] - &material[0][1] * &material[1][0];
    SiteFactor::new(trace, determinant)
}

#[cfg(test)]
#[path = "machine/tests.rs"]
mod tests;
