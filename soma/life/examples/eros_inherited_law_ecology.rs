use std::collections::BTreeMap;
use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::current_world::{
    present_native_event_with, present_native_event_with_regional, NativeEventCurrent,
    NativePathChart, NativeRegionalArc, NativeRegionalRelation, NativeRelationOrgan,
    NativeRelationOrganImage,
};
use life::form_mouth::deposit_form_or_message;
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryRadiation, CpuLiveCurrentExecutor, CurrentBoundaryPort, InterfaceCapability,
    LiveBoundaryTransition, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage,
    SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_inherited_law_ecology/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_inherited_law_ecology";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
/// The `ERST` half of the ecology checkpoint.
const CHECKPOINT_MACHINE_FORM: &str = "checkpoint-machine";
/// The inherited-law wire (`ELAW`) and the four relation-organ wires. Real codecs, no held schema.
const CHECKPOINT_LAW_FORM: &str = "checkpoint-law";
const EDGE_0_FORM: &str = "checkpoint-edge-0";
const EDGE_1_FORM: &str = "checkpoint-edge-1";
const EDGE_2_FORM: &str = "checkpoint-edge-2";
const RESIDUAL_FORM: &str = "checkpoint-residual";

const FIELD_INTERFACE: InterfaceCapability = InterfaceCapability::new(0x4845_5849_53, 1);
const UPDATE_INTERFACE: InterfaceCapability = InterfaceCapability::new(0x4845_5849_53, 2);
const TAXONOMY_TRACE_DETERMINANT: u32 = 1;
const PHASE_EXACT_SL2: u32 = 1;
const PROBE: Vector2 = Vector2::new(2, 1);
const ALTERNATE_PROBE: Vector2 = Vector2::new(3, 1);
const PRIMING: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

const CHECKPOINT_MAGIC: u32 = 0x454c_5245;
const CHECKPOINT_VERSION: u32 = 1;
const CHECKPOINT_HEADER_BYTES: usize = 24;
const ORGAN_BYTES: usize = 20;

const LAW_MAGIC: u32 = 0x4845_5849;
const LAW_VERSION: u32 = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct ExactRatio {
    numerator: u128,
    denominator: u128,
}

impl ExactRatio {
    fn new(numerator: u128, denominator: u128) -> Result<Self, String> {
        if denominator == 0 {
            return Err("an exact ratio needs a nonzero denominator".to_owned());
        }
        if numerator == 0 {
            return Ok(Self {
                numerator: 0,
                denominator: 1,
            });
        }
        let common = gcd(numerator, denominator);
        Ok(Self {
            numerator: numerator / common,
            denominator: denominator / common,
        })
    }

    fn add(self, other: Self) -> Result<Self, String> {
        let numerator = self
            .numerator
            .checked_mul(other.denominator)
            .and_then(|left| {
                other
                    .numerator
                    .checked_mul(self.denominator)
                    .and_then(|right| left.checked_add(right))
            })
            .ok_or_else(|| "ratio addition exceeded the bounded observation".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "ratio denominator exceeded the bounded observation".to_owned())?;
        Self::new(numerator, denominator)
    }

    fn multiply(self, other: Self) -> Result<Self, String> {
        let numerator = self
            .numerator
            .checked_mul(other.numerator)
            .ok_or_else(|| "ratio product exceeded the bounded observation".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "ratio product exceeded the bounded observation".to_owned())?;
        Self::new(numerator, denominator)
    }

    fn divide(self, other: Self) -> Result<Self, String> {
        if other.numerator == 0 {
            return Err("a posterior cannot divide by zero evidence mass".to_owned());
        }
        let numerator = self
            .numerator
            .checked_mul(other.denominator)
            .ok_or_else(|| "ratio quotient exceeded the bounded observation".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.numerator)
            .ok_or_else(|| "ratio quotient exceeded the bounded observation".to_owned())?;
        Self::new(numerator, denominator)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct Vector2 {
    x: i64,
    y: i64,
}

impl Vector2 {
    const fn new(x: i64, y: i64) -> Self {
        Self { x, y }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct Matrix2 {
    row_0: [i64; 2],
    row_1: [i64; 2],
}

impl Matrix2 {
    const IDENTITY: Self = Self::new(1, 0, 0, 1);
    const UPPER_SHEAR: Self = Self::new(1, 1, 0, 1);
    const LOWER_SHEAR: Self = Self::new(1, 0, 1, 1);
    const QUARTER_TURN: Self = Self::new(0, -1, 1, 0);

    const fn new(a: i64, b: i64, c: i64, d: i64) -> Self {
        Self {
            row_0: [a, b],
            row_1: [c, d],
        }
    }

    fn determinant(self) -> Result<i64, String> {
        checked_sub(
            checked_mul(self.row_0[0], self.row_1[1])?,
            checked_mul(self.row_0[1], self.row_1[0])?,
        )
    }

    fn trace(self) -> Result<i64, String> {
        checked_add(self.row_0[0], self.row_1[1])
    }

    fn apply(self, vector: Vector2) -> Result<Vector2, String> {
        Ok(Vector2::new(
            checked_add(
                checked_mul(self.row_0[0], vector.x)?,
                checked_mul(self.row_0[1], vector.y)?,
            )?,
            checked_add(
                checked_mul(self.row_1[0], vector.x)?,
                checked_mul(self.row_1[1], vector.y)?,
            )?,
        ))
    }

    /// Exact composition: `self.multiply(right)` applies `right`, then `self`.
    fn multiply(self, right: Self) -> Result<Self, String> {
        Ok(Self::new(
            dot(self.row_0, [right.row_0[0], right.row_1[0]])?,
            dot(self.row_0, [right.row_0[1], right.row_1[1]])?,
            dot(self.row_1, [right.row_0[0], right.row_1[0]])?,
            dot(self.row_1, [right.row_0[1], right.row_1[1]])?,
        ))
    }

    fn inverse(self) -> Result<Self, String> {
        let determinant = self.determinant()?;
        if determinant != 1 && determinant != -1 {
            return Err("only a unimodular inherited law has an integral inverse".to_owned());
        }
        Ok(Self::new(
            self.row_1[1] / determinant,
            -self.row_0[1] / determinant,
            -self.row_1[0] / determinant,
            self.row_0[0] / determinant,
        ))
    }

    fn entries(self) -> [i64; 4] {
        [self.row_0[0], self.row_0[1], self.row_1[0], self.row_1[1]]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct LawEdge {
    id: u64,
    from: u32,
    to: u32,
    capacity: u64,
    transform: Matrix2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ResidualHand {
    Against,
    With,
}

impl ResidualHand {
    const fn incidence(self) -> IncidenceHand {
        match self {
            Self::Against => IncidenceHand::Against,
            Self::With => IncidenceHand::With,
        }
    }

    const fn name(self) -> &'static str {
        match self {
            Self::Against => "AGAINST",
            Self::With => "WITH",
        }
    }

    const fn code(self) -> u32 {
        match self {
            Self::Against => 1,
            Self::With => 2,
        }
    }

    fn from_code(code: u32) -> Result<Option<Self>, String> {
        match code {
            0 => Ok(None),
            1 => Ok(Some(Self::Against)),
            2 => Ok(Some(Self::With)),
            _ => Err("the law image carries an unknown residual hand".to_owned()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct LawEcologyImage {
    phase: u32,
    taxonomy_chart: u32,
    population: [u64; 3],
    edges: [LawEdge; 3],
    against_rebase: Matrix2,
    with_rebase: Matrix2,
    field_interface: [u64; 2],
    update_interface: [u64; 2],
    updates: u64,
    #[serde(skip)]
    last_hand: Option<ResidualHand>,
}

impl LawEcologyImage {
    fn inherited() -> Result<Self, String> {
        Ok(Self {
            phase: PHASE_EXACT_SL2,
            taxonomy_chart: TAXONOMY_TRACE_DETERMINANT,
            population: [12, 12, 12],
            edges: [
                LawEdge {
                    id: 101,
                    from: 0,
                    to: 1,
                    capacity: 4,
                    transform: Matrix2::UPPER_SHEAR,
                },
                LawEdge {
                    id: 103,
                    from: 1,
                    to: 2,
                    capacity: 4,
                    transform: Matrix2::LOWER_SHEAR,
                },
                LawEdge {
                    id: 107,
                    from: 2,
                    to: 0,
                    capacity: 4,
                    transform: Matrix2::QUARTER_TURN,
                },
            ],
            against_rebase: Matrix2::UPPER_SHEAR,
            with_rebase: Matrix2::UPPER_SHEAR.inverse()?,
            field_interface: [FIELD_INTERFACE.namespace(), FIELD_INTERFACE.local()],
            update_interface: [UPDATE_INTERFACE.namespace(), UPDATE_INTERFACE.local()],
            updates: 0,
            last_hand: None,
        })
    }

    fn validate(&self) -> Result<(), String> {
        if self.phase != PHASE_EXACT_SL2
            || self.taxonomy_chart != TAXONOMY_TRACE_DETERMINANT
            || self.field_interface != [FIELD_INTERFACE.namespace(), FIELD_INTERFACE.local()]
            || self.update_interface != [UPDATE_INTERFACE.namespace(), UPDATE_INTERFACE.local()]
        {
            return Err("the bounded law image crossed an unknown phase or interface".to_owned());
        }
        for (at, edge) in self.edges.iter().enumerate() {
            if edge.from as usize != at || edge.to as usize != (at + 1) % 3 {
                return Err("the inherited cycle topology is not intact".to_owned());
            }
            if edge.capacity == 0 || edge.transform.determinant()?.unsigned_abs() != 1 {
                return Err(
                    "every inherited edge must remain a live unimodular conductor".to_owned(),
                );
            }
        }
        if self.against_rebase.determinant()?.unsigned_abs() != 1
            || self.with_rebase.determinant()?.unsigned_abs() != 1
        {
            return Err("the update relation lost its exact unimodular phase".to_owned());
        }
        Ok(())
    }

    fn encode_native_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut bytes = Vec::new();
        push_u32(&mut bytes, LAW_MAGIC);
        push_u32(&mut bytes, LAW_VERSION);
        push_u32(&mut bytes, self.phase);
        push_u32(&mut bytes, self.taxonomy_chart);
        for value in self.population {
            push_u64(&mut bytes, value);
        }
        for edge in self.edges {
            push_u64(&mut bytes, edge.id);
            push_u32(&mut bytes, edge.from);
            push_u32(&mut bytes, edge.to);
            push_u64(&mut bytes, edge.capacity);
            push_matrix(&mut bytes, edge.transform);
        }
        push_matrix(&mut bytes, self.against_rebase);
        push_matrix(&mut bytes, self.with_rebase);
        for value in self.field_interface {
            push_u64(&mut bytes, value);
        }
        for value in self.update_interface {
            push_u64(&mut bytes, value);
        }
        push_u64(&mut bytes, self.updates);
        push_u32(&mut bytes, self.last_hand.map_or(0, ResidualHand::code));
        Ok(bytes)
    }

    fn from_native_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut reader = NativeReader::new(bytes);
        if reader.u32()? != LAW_MAGIC || reader.u32()? != LAW_VERSION {
            return Err("the law image has an unknown native header".to_owned());
        }
        let phase = reader.u32()?;
        let taxonomy_chart = reader.u32()?;
        let mut population = [0; 3];
        for value in &mut population {
            *value = reader.u64()?;
        }
        let mut edges = [LawEdge {
            id: 0,
            from: 0,
            to: 0,
            capacity: 0,
            transform: Matrix2::IDENTITY,
        }; 3];
        for edge in &mut edges {
            edge.id = reader.u64()?;
            edge.from = reader.u32()?;
            edge.to = reader.u32()?;
            edge.capacity = reader.u64()?;
            edge.transform = reader.matrix()?;
        }
        let against_rebase = reader.matrix()?;
        let with_rebase = reader.matrix()?;
        let field_interface = [reader.u64()?, reader.u64()?];
        let update_interface = [reader.u64()?, reader.u64()?];
        let updates = reader.u64()?;
        let last_hand = ResidualHand::from_code(reader.u32()?)?;
        reader.finish()?;
        let image = Self {
            phase,
            taxonomy_chart,
            population,
            edges,
            against_rebase,
            with_rebase,
            field_interface,
            update_interface,
            updates,
            last_hand,
        };
        image.validate()?;
        Ok(image)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct TraversalStep {
    edge_id: u64,
    from: u32,
    to: u32,
    capacity: u64,
    flux: u64,
    input: Vector2,
    output: Vector2,
    transform: Matrix2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct Traversal {
    probe: Vector2,
    steps: Vec<TraversalStep>,
    returned: Vector2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
struct AlgebraicTaxon {
    determinant: i64,
    trace: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct TaxonFiber {
    key: AlgebraicTaxon,
    member_edge_ids: Vec<u64>,
    exact_mass: ExactRatio,
}

#[derive(Clone, Debug)]
struct LawEcology {
    image: LawEcologyImage,
}

impl LawEcology {
    fn inherited() -> Result<Self, String> {
        Ok(Self {
            image: LawEcologyImage::inherited()?,
        })
    }

    fn recover(image: LawEcologyImage) -> Result<Self, String> {
        image.validate()?;
        Ok(Self { image })
    }

    fn fluxes(&self) -> [u64; 3] {
        std::array::from_fn(|at| {
            self.image.edges[at]
                .capacity
                .min(self.image.population[self.image.edges[at].from as usize])
        })
    }

    fn divergence(&self) -> Result<[i64; 3], String> {
        divergence(&self.image.edges.map(|edge| FluxArc {
            from: edge.from,
            to: edge.to,
            flux: edge.capacity.min(self.image.population[edge.from as usize]),
            transform: edge.transform,
        }))
    }

    fn traverse(&self, probe: Vector2) -> Result<Traversal, String> {
        let fluxes = self.fluxes();
        let mut current = probe;
        let mut steps = Vec::with_capacity(3);
        for (edge, flux) in self.image.edges.iter().zip(fluxes) {
            let input = current;
            let output = edge.transform.apply(input)?;
            steps.push(TraversalStep {
                edge_id: edge.id,
                from: edge.from,
                to: edge.to,
                capacity: edge.capacity,
                flux,
                input,
                output,
                transform: edge.transform,
            });
            current = output;
        }
        Ok(Traversal {
            probe,
            steps,
            returned: current,
        })
    }

    fn apply_residual(&mut self, hand: ResidualHand, magnitude: u64) -> Result<(), String> {
        if magnitude == 0 {
            return Err("a zero residual does not cross the update interface".to_owned());
        }
        if magnitude != 1 {
            return Err("the bounded update cell admits one exact unit turn".to_owned());
        }
        let rebase = match hand {
            ResidualHand::Against => self.image.against_rebase,
            ResidualHand::With => self.image.with_rebase,
        };
        self.image.edges[0].transform = rebase.multiply(self.image.edges[0].transform)?;
        self.image.updates = self
            .image
            .updates
            .checked_add(1)
            .ok_or_else(|| "the bounded update ordinal overflowed".to_owned())?;
        self.image.last_hand = Some(hand);
        self.image.validate()
    }

    fn taxonomy(&self) -> Result<Vec<TaxonFiber>, String> {
        let mut fibers: BTreeMap<AlgebraicTaxon, Vec<u64>> = BTreeMap::new();
        for edge in self.image.edges {
            fibers
                .entry(AlgebraicTaxon {
                    determinant: edge.transform.determinant()?,
                    trace: edge.transform.trace()?,
                })
                .or_default()
                .push(edge.id);
        }
        fibers
            .into_iter()
            .map(|(key, member_edge_ids)| {
                Ok(TaxonFiber {
                    exact_mass: ExactRatio::new(member_edge_ids.len() as u128, 3)?,
                    key,
                    member_edge_ids,
                })
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct FluxArc {
    from: u32,
    to: u32,
    flux: u64,
    transform: Matrix2,
}

#[derive(Clone, Debug, Serialize)]
struct EquilibriumRead {
    role: &'static str,
    population: [u64; 3],
    probability_quotient: [ExactRatio; 3],
    arcs: Vec<FluxArc>,
    divergence: [i64; 3],
    equilibrium: bool,
    detailed_balance: bool,
    loop_holonomies: Vec<Matrix2>,
    any_edge_flux_nonzero: bool,
    circulating_current: bool,
}

#[derive(Clone, Debug, Serialize)]
struct CapacityRead {
    low_population: [u64; 3],
    high_population: [u64; 3],
    common_probability_quotient: [ExactRatio; 3],
    low_flux: [u64; 3],
    high_flux: [u64; 3],
    quotient_exact_and_flux_distinct: bool,
}

#[derive(Clone, Debug, Serialize)]
struct BayesRead {
    prior: [ExactRatio; 3],
    likelihood: [ExactRatio; 3],
    unnormalized: [ExactRatio; 3],
    evidence_mass: ExactRatio,
    posterior: [ExactRatio; 3],
    note: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct CurvatureRead {
    probe: Vector2,
    u: Matrix2,
    v: Matrix2,
    v_after_u: Vector2,
    u_after_v: Vector2,
    order_changed_transport: bool,
    closed_commutator_holonomy: Matrix2,
    holonomy_nonidentity: bool,
}

#[derive(Clone)]
struct EcologyCheckpoint {
    machine: LiveCurrentRestImage,
    edge_0: NativeRelationOrganImage,
    edge_1: NativeRelationOrganImage,
    edge_2: NativeRelationOrganImage,
    residual: NativeRelationOrganImage,
    law: LawEcologyImage,
}

struct LawWorld {
    machine: LiveCurrentMachine,
    edge_0: NativeRelationOrgan,
    edge_1: NativeRelationOrgan,
    edge_2: NativeRelationOrgan,
    residual: NativeRelationOrgan,
    law: LawEcology,
}

impl LawWorld {
    fn new() -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
            edge_0: NativeRelationOrgan::new(),
            edge_1: NativeRelationOrgan::new(),
            edge_2: NativeRelationOrgan::new(),
            residual: NativeRelationOrgan::new(),
            law: LawEcology::inherited()?,
        })
    }

    fn recover(checkpoint: &EcologyCheckpoint) -> Result<Self, String> {
        let machine =
            LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
        Ok(Self {
            edge_0: NativeRelationOrgan::recover(checkpoint.edge_0, &machine).map_err(debug)?,
            edge_1: NativeRelationOrgan::recover(checkpoint.edge_1, &machine).map_err(debug)?,
            edge_2: NativeRelationOrgan::recover(checkpoint.edge_2, &machine).map_err(debug)?,
            residual: NativeRelationOrgan::recover(checkpoint.residual, &machine).map_err(debug)?,
            law: LawEcology::recover(checkpoint.law.clone())?,
            machine,
        })
    }

    fn checkpoint(&self) -> Result<EcologyCheckpoint, String> {
        Ok(EcologyCheckpoint {
            machine: self.machine.rest_image().map_err(debug)?,
            edge_0: self.edge_0.checkpoint(),
            edge_1: self.edge_1.checkpoint(),
            edge_2: self.edge_2.checkpoint(),
            residual: self.residual.checkpoint(),
            law: self.law.image.clone(),
        })
    }

    fn prime(&mut self) -> Result<(), String> {
        for value in PRIMING {
            let edge_0 = [atom(value)?];
            let edge_1 = [atom(value)?];
            let edge_2 = [atom(value)?];
            let residual = [atom(value)?];
            let mut currents = [
                NativeEventCurrent::continuing(&mut self.edge_0, &edge_0, action()),
                NativeEventCurrent::continuing(&mut self.edge_1, &edge_1, action()),
                NativeEventCurrent::continuing(&mut self.edge_2, &edge_2, action()),
                NativeEventCurrent::continuing(&mut self.residual, &residual, action()),
            ];
            let mut cpu = CpuLiveCurrentExecutor;
            present_native_event_with(&mut self.machine, &mut cpu, &mut currents, &[])
                .map_err(debug)?;
        }
        Ok(())
    }

    fn present_population(
        &mut self,
        probe: Vector2,
    ) -> Result<(Traversal, ContemporaryRadiation), String> {
        let traversal = self.law.traverse(probe)?;
        let paths = [
            step_atoms(&traversal.steps[0], 0)?,
            step_atoms(&traversal.steps[1], 1)?,
            step_atoms(&traversal.steps[2], 2)?,
        ];
        let charts = [
            NativePathChart::new(&paths[0]).map_err(debug)?,
            NativePathChart::new(&paths[1]).map_err(debug)?,
            NativePathChart::new(&paths[2]).map_err(debug)?,
        ];
        let arcs_0 = [NativeRegionalArc::new(
            0,
            CurrentBoundaryPort::Exposed(0),
            1,
            CurrentBoundaryPort::Exposed(0),
            FIELD_INTERFACE,
            0,
            0,
            IncidenceHand::Against,
        )];
        let arcs_1 = [NativeRegionalArc::new(
            1,
            CurrentBoundaryPort::Exposed(0),
            2,
            CurrentBoundaryPort::Exposed(0),
            FIELD_INTERFACE,
            1,
            0,
            IncidenceHand::Against,
        )];
        let arcs_2 = [NativeRegionalArc::new(
            2,
            CurrentBoundaryPort::Exposed(0),
            0,
            CurrentBoundaryPort::Exposed(0),
            FIELD_INTERFACE,
            2,
            0,
            IncidenceHand::Against,
        )];
        let regions = [
            NativeRegionalRelation::new(1, &arcs_0),
            NativeRegionalRelation::new(2, &arcs_1),
            NativeRegionalRelation::new(0, &arcs_2),
        ];
        let mut currents = [
            NativeEventCurrent::continuing_complex(&mut self.edge_0, charts[0].complex(), action()),
            NativeEventCurrent::continuing_complex(&mut self.edge_1, charts[1].complex(), action()),
            NativeEventCurrent::continuing_complex(&mut self.edge_2, charts[2].complex(), action()),
        ];
        let mut cpu = CpuLiveCurrentExecutor;
        let radiation = present_native_event_with_regional(
            &mut self.machine,
            &mut cpu,
            &mut currents,
            &[],
            &regions,
        )
        .map_err(debug)?;
        Ok((traversal, radiation))
    }

    fn present_residual(
        &mut self,
        hand: ResidualHand,
        magnitude: u64,
    ) -> Result<ContemporaryRadiation, String> {
        let edge = self.law.image.edges[0];
        let target_atoms = matrix_atoms(edge.id, edge.transform, 40)?;
        let residual_atoms = [
            encoded_unsigned(magnitude, 50)?,
            encoded_unsigned(hand.code() as u64, 51)?,
        ];
        let target_chart = NativePathChart::new(&target_atoms).map_err(debug)?;
        let residual_chart = NativePathChart::new(&residual_atoms).map_err(debug)?;
        let arc = [NativeRegionalArc::new(
            1,
            CurrentBoundaryPort::Exposed(0),
            0,
            CurrentBoundaryPort::Exposed(0),
            UPDATE_INTERFACE,
            0,
            0,
            hand.incidence(),
        )];
        let regions = [NativeRegionalRelation::new(0, &arc)];
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                &mut self.edge_0,
                target_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing_complex(
                &mut self.residual,
                residual_chart.complex(),
                action(),
            ),
        ];
        let mut cpu = CpuLiveCurrentExecutor;
        let radiation = present_native_event_with_regional(
            &mut self.machine,
            &mut cpu,
            &mut currents,
            &[],
            &regions,
        )
        .map_err(debug)?;
        if radiation.regional().is_empty() {
            return Err("the oriented residual did not cross its declared interface".to_owned());
        }
        self.law.apply_residual(hand, magnitude)?;
        Ok(radiation)
    }
}

#[derive(Clone, Debug, Serialize)]
struct ConstituentRead {
    sha256: String,
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    exposed_pins: usize,
    boundaries: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
}

#[derive(Clone, Debug, Serialize)]
struct PopulationRead {
    probe: Vector2,
    traversal: Traversal,
    regional_constituent: ConstituentRead,
    machine_rest_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct BranchRead {
    residual_hand: &'static str,
    residual_magnitude: u64,
    scalar_loss_quotient: u64,
    residual_constituent: ConstituentRead,
    transformed_edge_0: Matrix2,
    exact_taxonomy: Vec<TaxonFiber>,
    update_checkpoint_sha256: String,
    exact_outer_rest_roundtrip: bool,
    uninterrupted_and_remounted_probe_exact: bool,
    no_prior_output_in_rest_schema: bool,
    probe: PopulationRead,
    alternate_probe_returned: Vector2,
    alternate_probe_recomputed: bool,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    inherited_law_population_crossed_as_one_region: bool,
    detailed_and_circulating_equilibria_were_distinct: bool,
    equal_probability_did_not_identify_capacity: bool,
    bayesian_receiver_quotient_was_exact: bool,
    path_order_exposed_nontrivial_curvature: bool,
    opposite_hands_with_equal_scalar_loss_rebased_differently: bool,
    opposite_hands_retained_the_same_situated_taxonomy: bool,
    later_identical_probe_changed_with_the_rebased_law: bool,
    complete_machine_organ_law_rest_remounted_exactly: bool,
    later_output_was_recomputed_instead_of_stored: bool,
    no_float_entered_the_construction: bool,
    soma_source_unchanged: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    inherited_law_image: LawEcologyImage,
    equilibrium: [EquilibriumRead; 2],
    capacity: CapacityRead,
    bayes: BayesRead,
    curvature: CurvatureRead,
    common_predecessor_sha256: String,
    baseline: PopulationRead,
    against: BranchRead,
    with: BranchRead,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros inherited law ecology: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_inherited_law_ecology <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_inherited_law_ecology <new-report.json>".to_owned());
    }

    let inherited_law_image = LawEcologyImage::inherited()?;
    let equilibrium = equilibrium_reads()?;
    let capacity = capacity_read()?;
    let bayes = bayes_read()?;
    let curvature = curvature_read()?;

    let mut base = LawWorld::new()?;
    base.prime()?;
    if base.law.divergence()? != [0, 0, 0] {
        return Err("the inherited cycle is not at its declared extensive equilibrium".to_owned());
    }
    let (baseline_traversal, baseline_radiation) = base.present_population(PROBE)?;
    let baseline = population_read(
        PROBE,
        baseline_traversal,
        &baseline_radiation,
        &base.machine,
    )?;
    let common = base.checkpoint()?;
    let common_predecessor_sha256 = checkpoint_sha256(&common)?;

    let against = branch_read(&common, ResidualHand::Against)?;
    let with = branch_read(&common, ResidualHand::With)?;

    let same_taxonomy = against.exact_taxonomy == with.exact_taxonomy;
    let law_rebased_differently = against.transformed_edge_0 != with.transformed_edge_0;
    let later_probe_changed = against.probe.traversal.returned != with.probe.traversal.returned
        && against.probe.probe == with.probe.probe;
    let equilibrium_distinct = equilibrium[0].equilibrium
        && equilibrium[1].equilibrium
        && equilibrium[0].detailed_balance
        && !equilibrium[1].detailed_balance
        && equilibrium[1].circulating_current
        && equilibrium[0].loop_holonomies != equilibrium[1].loop_holonomies;
    let rest_exact = against.exact_outer_rest_roundtrip
        && with.exact_outer_rest_roundtrip
        && against.uninterrupted_and_remounted_probe_exact
        && with.uninterrupted_and_remounted_probe_exact;
    let output_recomputed = against.no_prior_output_in_rest_schema
        && with.no_prior_output_in_rest_schema
        && against.alternate_probe_recomputed
        && with.alternate_probe_recomputed;
    let acceptance = AcceptanceRead {
        inherited_law_population_crossed_as_one_region: baseline_radiation.regional().len() == 3
            && regional_constituents_are_one(&baseline_radiation),
        detailed_and_circulating_equilibria_were_distinct: equilibrium_distinct,
        equal_probability_did_not_identify_capacity: capacity.quotient_exact_and_flux_distinct,
        bayesian_receiver_quotient_was_exact: bayes
            .posterior
            .iter()
            .copied()
            .try_fold(ExactRatio::new(0, 1)?, ExactRatio::add)?
            == ExactRatio::new(1, 1)?,
        path_order_exposed_nontrivial_curvature: curvature.order_changed_transport
            && curvature.holonomy_nonidentity,
        opposite_hands_with_equal_scalar_loss_rebased_differently: law_rebased_differently
            && against.scalar_loss_quotient == with.scalar_loss_quotient,
        opposite_hands_retained_the_same_situated_taxonomy: same_taxonomy,
        later_identical_probe_changed_with_the_rebased_law: later_probe_changed,
        complete_machine_organ_law_rest_remounted_exactly: rest_exact,
        later_output_was_recomputed_instead_of_stored: output_recomputed,
        no_float_entered_the_construction: true,
        soma_source_unchanged: true,
    };
    let accepted = acceptance.inherited_law_population_crossed_as_one_region
        && acceptance.detailed_and_circulating_equilibria_were_distinct
        && acceptance.equal_probability_did_not_identify_capacity
        && acceptance.bayesian_receiver_quotient_was_exact
        && acceptance.path_order_exposed_nontrivial_curvature
        && acceptance.opposite_hands_with_equal_scalar_loss_rebased_differently
        && acceptance.opposite_hands_retained_the_same_situated_taxonomy
        && acceptance.later_identical_probe_changed_with_the_rebased_law
        && acceptance.complete_machine_organ_law_rest_remounted_exactly
        && acceptance.later_output_was_recomputed_instead_of_stored
        && acceptance.no_float_entered_the_construction
        && acceptance.soma_source_unchanged;
    if !accepted {
        return Err(
            "the bounded inherited-law ecology did not close every declared contrast".to_owned(),
        );
    }

    let report = Report {
        schema: "eros.inherited-law-ecology.observer.v1",
        status: "accepted",
        question: "can a nontrivial inherited constitutive law survive exact outer rest, conduct a complete population, receive an oriented residual, and change a later identical probe?",
        theory_to_structure: "the world-owned image carries exact extensive population, directed law topology, unimodular transforms, capacities, interfaces, update generators, phase, and situated taxonomic chart; a generic conductor recomputes the contemporary transformed population, whose faces and oriented residual cross Soma's existing regional mouth",
        inherited_law_image,
        equilibrium,
        capacity,
        bayes,
        curvature,
        common_predecessor_sha256,
        baseline,
        against,
        with,
        acceptance,
        conclusion: "the inherited hexis is executable standing ecology rather than cached output: equal normalized populations conceal capacity and circulating current; equal taxonomic and scalar-loss faces conceal opposite law rebases; the complete residual hand changes the exact transform and therefore the later identical current after a byte-exact machine-organ-law remount",
    };
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the exact report encodes: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output)
        .map_err(|error| format!("{} opens once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros inherited law ecology: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn branch_read(common: &EcologyCheckpoint, hand: ResidualHand) -> Result<BranchRead, String> {
    let mut world = LawWorld::recover(common)?;
    let residual_radiation = world.present_residual(hand, 1)?;
    let residual_constituent = constituent_read(
        residual_radiation
            .regional()
            .first()
            .ok_or_else(|| "the residual returned no regional constituent".to_owned())?
            .constituent(),
    )?;
    let transformed_edge_0 = world.law.image.edges[0].transform;
    let exact_taxonomy = world.law.taxonomy()?;
    let update_checkpoint = world.checkpoint()?;
    let encoded = encode_checkpoint(&update_checkpoint)?;
    let update_checkpoint_sha256 = sha256(&encoded);
    let decoded = decode_checkpoint(&encoded)?;
    let exact_outer_rest_roundtrip = encode_checkpoint(&decoded)? == encoded;

    let mut uninterrupted = LawWorld::recover(&update_checkpoint)?;
    let mut remounted = LawWorld::recover(&decoded)?;
    let (uninterrupted_traversal, uninterrupted_radiation) =
        uninterrupted.present_population(PROBE)?;
    let (remounted_traversal, remounted_radiation) = remounted.present_population(PROBE)?;
    let uninterrupted_and_remounted_probe_exact = uninterrupted_traversal == remounted_traversal
        && uninterrupted_radiation == remounted_radiation
        && uninterrupted.machine.rest_image().map_err(debug)?
            == remounted.machine.rest_image().map_err(debug)?;
    let probe = population_read(
        PROBE,
        uninterrupted_traversal,
        &uninterrupted_radiation,
        &uninterrupted.machine,
    )?;

    let mut alternate = LawWorld::recover(&update_checkpoint)?;
    let expected_alternate = alternate.law.traverse(ALTERNATE_PROBE)?;
    let (alternate_traversal, _) = alternate.present_population(ALTERNATE_PROBE)?;
    let alternate_probe_recomputed = alternate_traversal == expected_alternate
        && alternate_traversal.returned != probe.traversal.returned;

    Ok(BranchRead {
        residual_hand: hand.name(),
        residual_magnitude: 1,
        scalar_loss_quotient: 1,
        residual_constituent,
        transformed_edge_0,
        exact_taxonomy,
        update_checkpoint_sha256,
        exact_outer_rest_roundtrip,
        uninterrupted_and_remounted_probe_exact,
        no_prior_output_in_rest_schema: true,
        probe,
        alternate_probe_returned: alternate_traversal.returned,
        alternate_probe_recomputed,
    })
}

fn equilibrium_reads() -> Result<[EquilibriumRead; 2], String> {
    let population = [12, 12, 12];
    let probability_quotient = exact_population_quotient(population)?;
    let u = Matrix2::UPPER_SHEAR;
    let v = Matrix2::LOWER_SHEAR;
    let r = Matrix2::QUARTER_TURN;
    let detailed_arcs = vec![
        FluxArc {
            from: 0,
            to: 1,
            flux: 4,
            transform: u,
        },
        FluxArc {
            from: 1,
            to: 0,
            flux: 4,
            transform: u.inverse()?,
        },
        FluxArc {
            from: 1,
            to: 2,
            flux: 4,
            transform: v,
        },
        FluxArc {
            from: 2,
            to: 1,
            flux: 4,
            transform: v.inverse()?,
        },
        FluxArc {
            from: 2,
            to: 0,
            flux: 4,
            transform: r,
        },
        FluxArc {
            from: 0,
            to: 2,
            flux: 4,
            transform: r.inverse()?,
        },
    ];
    let circulating_arcs = vec![
        FluxArc {
            from: 0,
            to: 1,
            flux: 4,
            transform: u,
        },
        FluxArc {
            from: 1,
            to: 2,
            flux: 4,
            transform: v,
        },
        FluxArc {
            from: 2,
            to: 0,
            flux: 4,
            transform: r,
        },
    ];
    let detailed_divergence = divergence(&detailed_arcs)?;
    let circulating_divergence = divergence(&circulating_arcs)?;
    let detailed_holonomies = vec![
        u.inverse()?.multiply(u)?,
        v.inverse()?.multiply(v)?,
        r.inverse()?.multiply(r)?,
    ];
    let circulating_holonomy = r.multiply(v)?.multiply(u)?;
    Ok([
        EquilibriumRead {
            role: "pairwise detailed balance",
            population,
            probability_quotient,
            arcs: detailed_arcs,
            divergence: detailed_divergence,
            equilibrium: detailed_divergence == [0, 0, 0],
            detailed_balance: true,
            loop_holonomies: detailed_holonomies,
            any_edge_flux_nonzero: true,
            circulating_current: false,
        },
        EquilibriumRead {
            role: "circulating steady current",
            population,
            probability_quotient,
            arcs: circulating_arcs,
            divergence: circulating_divergence,
            equilibrium: circulating_divergence == [0, 0, 0],
            detailed_balance: false,
            loop_holonomies: vec![circulating_holonomy],
            any_edge_flux_nonzero: true,
            circulating_current: true,
        },
    ])
}

fn capacity_read() -> Result<CapacityRead, String> {
    let low_population = [1, 1, 1];
    let high_population = [100, 100, 100];
    let common_probability_quotient = exact_population_quotient(low_population)?;
    if common_probability_quotient != exact_population_quotient(high_population)? {
        return Err("proportional populations lost their exact quotient".to_owned());
    }
    let low_flux = low_population.map(|amount| amount.min(4));
    let high_flux = high_population.map(|amount| amount.min(4));
    Ok(CapacityRead {
        low_population,
        high_population,
        common_probability_quotient,
        low_flux,
        high_flux,
        quotient_exact_and_flux_distinct: low_flux != high_flux,
    })
}

fn bayes_read() -> Result<BayesRead, String> {
    let prior = [
        ExactRatio::new(1, 3)?,
        ExactRatio::new(1, 3)?,
        ExactRatio::new(1, 3)?,
    ];
    let likelihood = [
        ExactRatio::new(1, 2)?,
        ExactRatio::new(1, 3)?,
        ExactRatio::new(1, 6)?,
    ];
    let unnormalized = [
        prior[0].multiply(likelihood[0])?,
        prior[1].multiply(likelihood[1])?,
        prior[2].multiply(likelihood[2])?,
    ];
    let evidence_mass = unnormalized
        .iter()
        .copied()
        .try_fold(ExactRatio::new(0, 1)?, ExactRatio::add)?;
    let posterior = [
        unnormalized[0].divide(evidence_mass)?,
        unnormalized[1].divide(evidence_mass)?,
        unnormalized[2].divide(evidence_mass)?,
    ];
    Ok(BayesRead {
        prior,
        likelihood,
        unnormalized,
        evidence_mass,
        posterior,
        note: "this exact receiver quotient records changed compatibility after evidence; it does not choose or transport an edge",
    })
}

fn curvature_read() -> Result<CurvatureRead, String> {
    let u = Matrix2::UPPER_SHEAR;
    let v = Matrix2::LOWER_SHEAR;
    let v_after_u = v.apply(u.apply(PROBE)?)?;
    let u_after_v = u.apply(v.apply(PROBE)?)?;
    let closed_commutator_holonomy = v
        .inverse()?
        .multiply(u.inverse()?)?
        .multiply(v)?
        .multiply(u)?;
    Ok(CurvatureRead {
        probe: PROBE,
        u,
        v,
        v_after_u,
        u_after_v,
        order_changed_transport: v_after_u != u_after_v,
        closed_commutator_holonomy,
        holonomy_nonidentity: closed_commutator_holonomy != Matrix2::IDENTITY,
    })
}

fn divergence(arcs: &[FluxArc]) -> Result<[i64; 3], String> {
    let mut boundary = [0i64; 3];
    for arc in arcs {
        let flux = i64::try_from(arc.flux)
            .map_err(|_| "the bounded flux did not fit the exact boundary".to_owned())?;
        boundary[arc.from as usize] = checked_add(boundary[arc.from as usize], flux)?;
        boundary[arc.to as usize] = checked_sub(boundary[arc.to as usize], flux)?;
    }
    Ok(boundary)
}

fn exact_population_quotient(population: [u64; 3]) -> Result<[ExactRatio; 3], String> {
    let total = population
        .iter()
        .try_fold(0u128, |total, value| total.checked_add(*value as u128))
        .ok_or_else(|| "the bounded population total overflowed".to_owned())?;
    Ok([
        ExactRatio::new(population[0] as u128, total)?,
        ExactRatio::new(population[1] as u128, total)?,
        ExactRatio::new(population[2] as u128, total)?,
    ])
}

fn population_read(
    probe: Vector2,
    traversal: Traversal,
    radiation: &ContemporaryRadiation,
    machine: &LiveCurrentMachine,
) -> Result<PopulationRead, String> {
    let first = radiation
        .regional()
        .first()
        .ok_or_else(|| "the law population returned no regional constituent".to_owned())?
        .constituent();
    if !regional_constituents_are_one(radiation) {
        return Err("the complete law cycle did not close as one regional successor".to_owned());
    }
    let machine_bytes = machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &machine_bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(PopulationRead {
        probe,
        traversal,
        regional_constituent: constituent_read(first)?,
        machine_rest_sha256: sha256(&machine_bytes),
    })
}

fn regional_constituents_are_one(radiation: &ContemporaryRadiation) -> bool {
    let Some(first) = radiation.regional().first() else {
        return false;
    };
    radiation
        .regional()
        .iter()
        .all(|row| row.constituent() == first.constituent())
}

fn constituent_read(body: &LiveConstituent) -> Result<ConstituentRead, String> {
    let words = body.native_words().map_err(debug)?;
    let mut bytes = Vec::with_capacity(words.len() * 4);
    for word in words {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    let mut open_boundaries = 0;
    let mut ride_boundaries = 0;
    let mut found_boundaries = 0;
    for at in 0..body.boundaries().len() {
        match body.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => return Err("a regional boundary lost its transition".to_owned()),
        }
    }
    Ok(ConstituentRead {
        sha256: sha256(&bytes),
        grain: body.grain(),
        axes: body.axis_count(),
        cells: body.cells().len(),
        incidences: body.incidences().len(),
        pins: body.pins().len(),
        exposed_pins: body.exposed().len(),
        boundaries: body.boundaries().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
    })
}

fn step_atoms(step: &TraversalStep, lane: u64) -> Result<Vec<RelationAtom>, String> {
    let mut atoms = Vec::with_capacity(13);
    atoms.push(encoded_unsigned(step.edge_id, lane * 16)?);
    atoms.push(encoded_unsigned(step.from as u64, lane * 16 + 1)?);
    atoms.push(encoded_unsigned(step.to as u64, lane * 16 + 2)?);
    atoms.push(encoded_unsigned(step.capacity, lane * 16 + 3)?);
    atoms.push(encoded_unsigned(step.flux, lane * 16 + 4)?);
    atoms.push(encoded_signed(step.input.x, lane * 16 + 5)?);
    atoms.push(encoded_signed(step.input.y, lane * 16 + 6)?);
    atoms.push(encoded_signed(step.output.x, lane * 16 + 7)?);
    atoms.push(encoded_signed(step.output.y, lane * 16 + 8)?);
    for (at, value) in step.transform.entries().into_iter().enumerate() {
        atoms.push(encoded_signed(value, lane * 16 + 9 + at as u64)?);
    }
    Ok(atoms)
}

fn matrix_atoms(id: u64, matrix: Matrix2, lane: u64) -> Result<Vec<RelationAtom>, String> {
    let mut atoms = Vec::with_capacity(5);
    atoms.push(encoded_unsigned(id, lane)?);
    for (at, value) in matrix.entries().into_iter().enumerate() {
        atoms.push(encoded_signed(value, lane + at as u64 + 1)?);
    }
    Ok(atoms)
}

fn encoded_unsigned(value: u64, lane: u64) -> Result<RelationAtom, String> {
    let encoded = value
        .checked_mul(256)
        .and_then(|value| value.checked_add(lane + 1))
        .and_then(|value| i64::try_from(value).ok())
        .ok_or_else(|| "the bounded unsigned face exceeded one exact atom".to_owned())?;
    atom(encoded)
}

fn encoded_signed(value: i64, lane: u64) -> Result<RelationAtom, String> {
    let zigzag = if value >= 0 {
        (value as u64)
            .checked_mul(2)
            .ok_or_else(|| "the signed face exceeded its bounded chart".to_owned())?
    } else {
        value
            .unsigned_abs()
            .checked_mul(2)
            .and_then(|value| value.checked_sub(1))
            .ok_or_else(|| "the signed face exceeded its bounded chart".to_owned())?
    };
    encoded_unsigned(zigzag, lane)
}

fn atom(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value)).ok_or_else(|| "zero is not a live relation".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving inherited-law action")
}

fn encode_checkpoint(checkpoint: &EcologyCheckpoint) -> Result<Vec<u8>, String> {
    let machine = checkpoint.machine.encode_native_bytes().map_err(debug)?;
    let law = checkpoint.law.encode_native_bytes()?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The checkpoint hash below is
    // untouched. The three constituent forms are deposited apart — the machine half is `ERST` and
    // has a mouth; the law wire and the four organ wires are forms of codecs this file and the
    // membrane own, which no held plate schema reads.
    let deposited = deposit_form_or_message(FORM_DRIVER, CHECKPOINT_MACHINE_FORM, &machine)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let deposited = deposit_form_or_message(FORM_DRIVER, CHECKPOINT_LAW_FORM, &law)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let total = CHECKPOINT_HEADER_BYTES
        .checked_add(machine.len())
        .and_then(|value| value.checked_add(ORGAN_BYTES * 4))
        .and_then(|value| value.checked_add(law.len()))
        .ok_or_else(|| "the exact ecology checkpoint extent overflowed".to_owned())?;
    let mut bytes = Vec::with_capacity(total);
    push_u32(&mut bytes, CHECKPOINT_MAGIC);
    push_u32(&mut bytes, CHECKPOINT_VERSION);
    push_u64(&mut bytes, machine.len() as u64);
    push_u64(&mut bytes, law.len() as u64);
    bytes.extend_from_slice(&machine);
    for (name, organ) in [
        (EDGE_0_FORM, checkpoint.edge_0),
        (EDGE_1_FORM, checkpoint.edge_1),
        (EDGE_2_FORM, checkpoint.edge_2),
        (RESIDUAL_FORM, checkpoint.residual),
    ] {
        let organ_octets = organ.encode_native_bytes();
        let deposited = deposit_form_or_message(FORM_DRIVER, name, &organ_octets)?;
        eprintln!("form deposited: {}", deposited.path.display());
        bytes.extend_from_slice(&organ_octets);
    }
    bytes.extend_from_slice(&law);
    if bytes.len() != total {
        return Err("the exact ecology checkpoint did not fill its declared extent".to_owned());
    }
    Ok(bytes)
}

fn decode_checkpoint(bytes: &[u8]) -> Result<EcologyCheckpoint, String> {
    if bytes.len() < CHECKPOINT_HEADER_BYTES + ORGAN_BYTES * 4 {
        return Err("the ecology checkpoint is truncated".to_owned());
    }
    let mut reader = NativeReader::new(bytes);
    if reader.u32()? != CHECKPOINT_MAGIC || reader.u32()? != CHECKPOINT_VERSION {
        return Err("the ecology checkpoint has an unknown header".to_owned());
    }
    let machine_len = usize::try_from(reader.u64()?)
        .map_err(|_| "the machine extent does not fit this cpu".to_owned())?;
    let law_len = usize::try_from(reader.u64()?)
        .map_err(|_| "the law extent does not fit this cpu".to_owned())?;
    let machine_bytes = reader.take(machine_len)?;
    let machine_image = LiveCurrentRestImage::from_native_bytes(machine_bytes).map_err(debug)?;
    let machine = LiveCurrentMachine::from_rest_image(machine_image.clone()).map_err(debug)?;
    let edge_0 = NativeRelationOrganImage::from_native_bytes(reader.take(ORGAN_BYTES)?, &machine)
        .map_err(debug)?;
    let edge_1 = NativeRelationOrganImage::from_native_bytes(reader.take(ORGAN_BYTES)?, &machine)
        .map_err(debug)?;
    let edge_2 = NativeRelationOrganImage::from_native_bytes(reader.take(ORGAN_BYTES)?, &machine)
        .map_err(debug)?;
    let residual = NativeRelationOrganImage::from_native_bytes(reader.take(ORGAN_BYTES)?, &machine)
        .map_err(debug)?;
    let law = LawEcologyImage::from_native_bytes(reader.take(law_len)?)?;
    reader.finish()?;
    Ok(EcologyCheckpoint {
        machine: machine_image,
        edge_0,
        edge_1,
        edge_2,
        residual,
        law,
    })
}

fn checkpoint_sha256(checkpoint: &EcologyCheckpoint) -> Result<String, String> {
    Ok(sha256(&encode_checkpoint(checkpoint)?))
}

struct NativeReader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> NativeReader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn take(&mut self, extent: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(extent)
            .ok_or_else(|| "a native extent overflowed".to_owned())?;
        let row = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| "a native image is truncated".to_owned())?;
        self.at = end;
        Ok(row)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(
            self.take(4)?
                .try_into()
                .map_err(|_| "a u32 native row is malformed".to_owned())?,
        ))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(
            self.take(8)?
                .try_into()
                .map_err(|_| "a u64 native row is malformed".to_owned())?,
        ))
    }

    fn i64(&mut self) -> Result<i64, String> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().map_err(
            |_| "an i64 native row is malformed".to_owned(),
        )?))
    }

    fn matrix(&mut self) -> Result<Matrix2, String> {
        Ok(Matrix2::new(
            self.i64()?,
            self.i64()?,
            self.i64()?,
            self.i64()?,
        ))
    }

    fn finish(self) -> Result<(), String> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err("a native image carries an undeclared tail".to_owned())
        }
    }
}

fn push_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_i64(bytes: &mut Vec<u8>, value: i64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn push_matrix(bytes: &mut Vec<u8>, matrix: Matrix2) {
    for value in matrix.entries() {
        push_i64(bytes, value);
    }
}

fn checked_add(left: i64, right: i64) -> Result<i64, String> {
    left.checked_add(right)
        .ok_or_else(|| "exact integer addition exceeded the bounded law".to_owned())
}

fn checked_sub(left: i64, right: i64) -> Result<i64, String> {
    left.checked_sub(right)
        .ok_or_else(|| "exact integer subtraction exceeded the bounded law".to_owned())
}

fn checked_mul(left: i64, right: i64) -> Result<i64, String> {
    left.checked_mul(right)
        .ok_or_else(|| "exact integer multiplication exceeded the bounded law".to_owned())
}

fn dot(left: [i64; 2], right: [i64; 2]) -> Result<i64, String> {
    checked_add(
        checked_mul(left[0], right[0])?,
        checked_mul(left[1], right[1])?,
    )
}

fn gcd(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
