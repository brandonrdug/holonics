//! **The Holon: the law and its ports, not its state.**
//!
//! `H = (K, ∂_A; Π; 𝒟; 𝓔; G; π)` ([object](../../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)):
//! the complex with its connection ([`crate::geometry::complex`]), ports ([`port`]), the Dirac
//! structure ([`dirac`]), element relations ([`element`], with [`deposition`] the only law that
//! changes them and [`reaction`] the learned power-neutral part), navigators
//! ([`crate::navigator`]) and restrictions ([`restriction`]). The law is [`law`]; [`conformance`]
//! holds the checks every Holon implementation passes. The two cells of the field are the helical
//! pair [`contact`] (slips, dissipates, addresses) and the ring [`parametron`] (stores,
//! oscillates, locks).
//!
//! [definition] A port Holon (`Holon/Element.PortHolon`) joins its Dirac structure on four
//! port kinds (storage `σ`, resistive `ρ`, external `π`, active `α`; `Holon/Element.Ports`)
//! with its storage form and resistance. A point of motion is admitted when its assembled bond
//! `(−v, Qx; f_R, −R f_R; f_P, e_P; f_A, e_A)` lies in `D` (`Holon/Element.PortHolon.Admits`),
//! and then the storage rate is dissipation, port and active power
//! (`Holon/Element.PortHolon.power_balance`, from `Holon/Element.power_assemble`).
//!
//! [definition] **Interaction is the recursion.** Interconnecting two Holons through shared
//! external ports returns a [`crate::holarchy::Holarchy`]: the joined whole, again a Holon, with
//! its retained constituents and typed gluing, or a typed [`crate::holarchy::GluingDefect`]
//! ([`Holon::interconnect`], defined in [`crate::holarchy`]; Lean `Holarchy/Join`). The whole's
//! port Holon has block storage and resistance and the composed Dirac structure
//! (`Holarchy/Join.joinHolon`; at the equal-effort, opposite-flow join it is
//! `Holon/Law.PortHolon.interconnect`, `Holarchy/Join.joinHolon_one`); energy and dissipation are
//! additive (`Holon/Law.storageEnergy_blocks`, `Holon/Law.dissipation_blocks`). A passive coholon
//! is the zero-storage receiver (`Holon/Law.passiveCoholon`).
//!
//! [definition] **The medium** `q̇ = (Ω − M + L) G q + B u` is the port Holon on the skew
//! interconnection `f_S = −Ω e_S − e_R − B e_P − e_A`, `f_R = e_S`, `f_P = Bᵀ e_S`, `f_A = e_S`
//! (`Holon/Conformance.mediumJ`, `Holon/Conformance.mediumHolon`,
//! `Holon/Conformance.medium_admits`), with the active block of
//! `Holon/Deposition.learned_energy_balance` added: `e_A = L f_A` gives `+L G q`.
//!
//! [definition] [`Holon`] is the law: the port Holon with its element relations, and the complex,
//! connection, ports, navigators and restrictions it is placed on. [`HolonState`] is a point on it.
//!
//! | Lean | Rust |
//! |---|---|
//! | `PortHolon`, `Ports`, `assemble` | [`PortHolon`], [`PortCounts`], [`PortHolon::assemble`] |
//! | `PortHolon.Admits`, `PortHolon.power_balance` | [`PortHolon::admits`], [`PortHolon::power_balance`] |
//! | `PortHolon.interconnect`, `mem_interconnect` | [`Holon::interconnect`] at unit gains ([`crate::holarchy`]) |
//! | `storageEnergy_blocks`, `dissipation_blocks` | tests of [`Holon::interconnect`] |
//! | `mediumJ`, `mediumHolon`, `medium_admits` | [`medium_structure`], [`PortHolon::medium`] |

pub mod conformance;
pub mod contact;
pub mod deposition;
pub mod dirac;
pub mod element;
pub mod law;
pub mod parametron;
pub mod port;
pub mod reaction;
pub mod restriction;

use crate::geometry::winding::WindingError;
use crate::ratio::Rat;
use num_traits::Zero;
use thiserror::Error;

use crate::geometry::complex::{CellComplex, ConnectionIncidence};
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{
    ActiveRelation, ElementRelation, Pump, ResistiveRelation, storage_effort, storage_energy,
};
use crate::holon::port::{Bond, Port};
use crate::holon::restriction::PortMap;
use crate::navigator::Navigator;
use crate::ratio::linear::inertia::{Inertia, InertiaError, SymmetricForm};
use crate::ratio::linear::vector::{at, dot, form_matrix, matrix, neg, quad};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

/// Every refusal of the Holon facets. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HolonError {
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("port {port} lies outside {ports} ports")]
    PortOutside { port: usize, ports: usize },
    #[error("port {port} is joined or listed twice")]
    PortJoinedTwice { port: usize },
    #[error("a port relabelling must be a permutation")]
    NotPermutation,
    #[error("the declared power dimension is not flow × effort")]
    UnitsMismatch,
    #[error("a skew-graph structure must satisfy Jᵀ = −J")]
    NotSkew,
    #[error("the structure is not isotropic: F Eᵀ + E Fᵀ ≠ 0")]
    NotIsotropic,
    #[error("the structure is not maximal: rank [F | E] = {rank}, ports = {ports}")]
    NotMaximal { rank: usize, ports: usize },
    #[error("∂∘∂ ≠ 0 at degree {degree}")]
    BoundaryNotClosed { degree: usize },
    #[error("edge {edge} is not an oriented graph edge of the declared vertices")]
    NotAGraphEdge { edge: usize },
    #[error("edge {edge} carries a zero transport; a connection value must be invertible")]
    ZeroTransport { edge: usize },
    #[error("the cell is not a closed walk at its base")]
    NotAClosedWalk,
    #[error("the relation is not passive; its symmetric part has inertia {inertia:?}")]
    NotPassive { inertia: Inertia },
    #[error("a clock step must be positive")]
    NonpositiveStep,
    #[error("{what} is singular")]
    Singular { what: &'static str },
    #[error("the step does not determine the motion: {nullity} free directions remain")]
    NotUniquelySolvable { nullity: usize },
    #[error("the step admits no motion: the constraints are inconsistent")]
    Inconsistent,
    #[error("the assembled bond is not admitted by the Dirac structure")]
    NotAdmitted,
    #[error(
        "the deposit exceeds (1 + ε) times the previous storage; the excess has inertia {inertia:?}"
    )]
    DepositExceedsBound { inertia: Inertia },
    #[error("1 + ε must be nonnegative")]
    NegativeGrowth,
    #[error("conformance check failed: {what}")]
    ConformanceFailed { what: &'static str },
    #[error("{what} is not supported: {reason}")]
    Unsupported {
        what: &'static str,
        reason: &'static str,
    },
    #[error("cell {cell} lies outside {cells} regions")]
    CellOutside { cell: usize, cells: usize },
    #[error("column {cell} of the degree-{degree} cellular map is not one unit entry")]
    NotACellularMap { degree: usize, cell: usize },
    #[error("fine block {block} does not lie inside the coarse block it restricts to")]
    BlockOutside { block: usize },
    /// Boxed: a gluing defect carries its witness bond, units or rates.
    #[error(transparent)]
    Gluing(Box<crate::holarchy::GluingDefect>),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Inertia(#[from] InertiaError),
    /// Boxed: the winding refusals carry exact big-number witnesses.
    #[error(transparent)]
    Winding(Box<WindingError>),
}

impl From<WindingError> for HolonError {
    fn from(error: WindingError) -> Self {
        Self::Winding(Box::new(error))
    }
}

/// [definition] The port counts of the four kinds, laid out `σ ⊕ ρ ⊕ π ⊕ α`
/// (`Holon/Element.Ports`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PortCounts {
    pub storage: usize,
    pub resistive: usize,
    pub external: usize,
    pub active: usize,
}

impl PortCounts {
    pub fn total(&self) -> usize {
        self.storage + self.resistive + self.external + self.active
    }

    pub fn resistive_offset(&self) -> usize {
        self.storage
    }

    pub fn external_offset(&self) -> usize {
        self.storage + self.resistive
    }

    pub fn active_offset(&self) -> usize {
        self.storage + self.resistive + self.external
    }
}

/// The four kinds of a bond, split.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KindBonds {
    pub storage: Bond,
    pub resistive: Bond,
    pub external: Bond,
    pub active: Bond,
}

/// [definition] **A port Holon** (`Holon/Element.PortHolon`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortHolon {
    dirac: DiracStructure,
    counts: PortCounts,
    storage: SymmetricForm,
    resistance: ResistiveRelation,
}

/// The point-of-motion balance terms of `Holon/Element.PortHolon.power_balance`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PowerBalance {
    /// `⟨Qx, v⟩`.
    pub storage_rate: Rat,
    /// `⟨f_R, R f_R⟩`.
    pub dissipated: Rat,
    /// `⟨e_P, f_P⟩`.
    pub port: Rat,
    /// `⟨e_A, f_A⟩`.
    pub active: Rat,
}

impl PowerBalance {
    /// `⟨Qx, v⟩ − (−dissipated + port + active)`: zero on every admitted point.
    pub fn residual(&self) -> Rat {
        &self.storage_rate - (-&self.dissipated + &self.port + &self.active)
    }
}

impl PortHolon {
    /// Validate shapes: `D` on `counts.total()` ports, `Q` on `σ`, `R` on `ρ` (certified passive).
    pub fn new(
        dirac: DiracStructure,
        counts: PortCounts,
        storage: SymmetricForm,
        resistance: ResistiveRelation,
    ) -> Result<Self, HolonError> {
        if dirac.ports() != counts.total() {
            return Err(HolonError::Shape {
                what: "Dirac ports",
                expected: counts.total(),
                found: dirac.ports(),
            });
        }
        if storage.extent() != counts.storage {
            return Err(HolonError::Shape {
                what: "storage form extent",
                expected: counts.storage,
                found: storage.extent(),
            });
        }
        let r = resistance.resistance();
        if r.rows() != counts.resistive || r.columns() != counts.resistive {
            return Err(HolonError::Shape {
                what: "resistance extent",
                expected: counts.resistive,
                found: r.rows(),
            });
        }
        Ok(Self {
            dirac,
            counts,
            storage,
            resistance,
        })
    }

    /// [definition] **The medium** `q̇ = (Ω − M + L) G q + B u` as a port Holon
    /// (`Holon/Conformance.mediumHolon`). With `active`, `σ` active ports carry `e_A = L e_S`.
    pub fn medium(
        omega: &ExactRatMatrix,
        resistance: &ExactRatMatrix,
        storage: SymmetricForm,
        input: &ExactRatMatrix,
        active: bool,
    ) -> Result<Self, HolonError> {
        let structure = medium_structure(omega, input, active)?;
        let sigma = omega.rows();
        Self::new(
            DiracStructure::skew_graph(&structure)?,
            PortCounts {
                storage: sigma,
                resistive: sigma,
                external: input.columns(),
                active: if active { sigma } else { 0 },
            },
            storage,
            ResistiveRelation::new(resistance.clone())?,
        )
    }

    pub fn dirac(&self) -> &DiracStructure {
        &self.dirac
    }

    pub fn counts(&self) -> PortCounts {
        self.counts
    }

    pub fn storage(&self) -> &SymmetricForm {
        &self.storage
    }

    pub fn resistance(&self) -> &ResistiveRelation {
        &self.resistance
    }

    /// `½⟨x, Qx⟩`.
    pub fn storage_energy(&self, x: &[Rat]) -> Result<Rat, HolonError> {
        storage_energy(&self.storage, x)
    }

    /// Assemble one bond from its four kinds (`Holon/Element.assemble`).
    pub fn assemble(&self, kinds: &KindBonds) -> Result<Bond, HolonError> {
        let c = self.counts;
        for (bond, expected, what) in [
            (&kinds.storage, c.storage, "storage bond"),
            (&kinds.resistive, c.resistive, "resistive bond"),
            (&kinds.external, c.external, "external bond"),
            (&kinds.active, c.active, "active bond"),
        ] {
            if bond.ports() != expected {
                return Err(HolonError::Shape {
                    what,
                    expected,
                    found: bond.ports(),
                });
            }
        }
        Ok(kinds
            .storage
            .concat(&kinds.resistive)
            .concat(&kinds.external)
            .concat(&kinds.active))
    }

    /// Split a bond into its four kinds.
    pub fn split(&self, bond: &Bond) -> Result<KindBonds, HolonError> {
        let c = self.counts;
        let range = |start: usize, len: usize| -> Vec<usize> { (start..start + len).collect() };
        Ok(KindBonds {
            storage: bond.select(&range(0, c.storage))?,
            resistive: bond.select(&range(c.resistive_offset(), c.resistive))?,
            external: bond.select(&range(c.external_offset(), c.external))?,
            active: bond.select(&range(c.active_offset(), c.active))?,
        })
    }

    /// The bond of a point of motion `(−v, Qx; f_R, −R f_R; f_P, e_P; f_A, e_A)`.
    #[allow(clippy::too_many_arguments)]
    pub fn motion_bond(
        &self,
        x: &[Rat],
        v: &[Rat],
        resistive_flow: &[Rat],
        external: &Bond,
        active: &Bond,
    ) -> Result<Bond, HolonError> {
        let storage = Bond::new(neg(v), storage_effort(&self.storage, x)?)?;
        let resistive = Bond::new(
            resistive_flow.to_vec(),
            neg(&self.resistance.resistance().apply(resistive_flow)?),
        )?;
        self.assemble(&KindBonds {
            storage,
            resistive,
            external: external.clone(),
            active: active.clone(),
        })
    }

    /// `Holon/Element.PortHolon.Admits`.
    pub fn admits(
        &self,
        x: &[Rat],
        v: &[Rat],
        resistive_flow: &[Rat],
        external: &Bond,
        active: &Bond,
    ) -> Result<bool, HolonError> {
        self.dirac
            .contains(&self.motion_bond(x, v, resistive_flow, external, active)?)
    }

    /// [proved-derived; implemented-exact] **The pointwise power balance** at an admitted point
    /// (`Holon/Element.PortHolon.power_balance`); refuses a point that is not admitted.
    pub fn power_balance(
        &self,
        x: &[Rat],
        v: &[Rat],
        resistive_flow: &[Rat],
        external: &Bond,
        active: &Bond,
    ) -> Result<PowerBalance, HolonError> {
        if !self.admits(x, v, resistive_flow, external, active)? {
            return Err(HolonError::NotAdmitted);
        }
        Ok(PowerBalance {
            storage_rate: dot(&storage_effort(&self.storage, x)?, v),
            dissipated: self.resistance.dissipation(resistive_flow)?,
            port: external.power(),
            active: active.power(),
        })
    }
}

/// [definition] **The skew interconnection of the medium** (`Holon/Conformance.mediumJ`) on
/// ports `σ ⊕ σ ⊕ μ ⊕ (σ | 0)`: `f_S = −Ω e_S − e_R − B e_P − e_A`, `f_R = e_S`, `f_P = Bᵀ e_S`,
/// `f_A = e_S`. Refuses a non-skew `Ω`.
pub fn medium_structure(
    omega: &ExactRatMatrix,
    input: &ExactRatMatrix,
    active: bool,
) -> Result<ExactRatMatrix, HolonError> {
    if !crate::ratio::linear::vector::is_skew(omega) {
        return Err(HolonError::NotSkew);
    }
    let sigma = omega.rows();
    if input.rows() != sigma {
        return Err(HolonError::Shape {
            what: "input rows",
            expected: sigma,
            found: input.rows(),
        });
    }
    let mu = input.columns();
    let alpha = if active { sigma } else { 0 };
    let n = 2 * sigma + mu + alpha;
    // Kind of an index: 0 storage, 1 resistive, 2 external, 3 active; and its local index.
    let kind = |i: usize| -> (u8, usize) {
        if i < sigma {
            (0, i)
        } else if i < 2 * sigma {
            (1, i - sigma)
        } else if i < 2 * sigma + mu {
            (2, i - 2 * sigma)
        } else {
            (3, i - 2 * sigma - mu)
        }
    };
    let delta = |a: usize, b: usize| {
        if a == b {
            Rat::from_integer(1.into())
        } else {
            Rat::zero()
        }
    };
    Ok(matrix(n, n, |row, column| {
        match (kind(row), kind(column)) {
            ((0, i), (0, j)) => -at(omega, i, j),
            ((0, i), (1, j)) | ((0, i), (3, j)) => -delta(i, j),
            ((1, i), (0, j)) | ((3, i), (0, j)) => delta(i, j),
            ((0, i), (2, k)) => -at(input, i, k),
            ((2, k), (0, i)) => at(input, i, k),
            _ => Rat::zero(),
        }
    })?)
}

/// [definition] **The Holon (the law)**: the port Holon and its element relations, placed on its
/// complex and connection with its oriented interior chain and the face each external port sits
/// on, with its named ports, navigators and restrictions (Lean `Holarchy/Join.Constituent`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Holon {
    port_holon: PortHolon,
    active: ActiveRelation,
    pump: Option<Pump>,
    ports: Option<Vec<Port>>,
    complex: Option<CellComplex>,
    connection: Option<ConnectionIncidence>,
    interior: Option<Vec<Rat>>,
    port_faces: Option<Vec<usize>>,
    navigators: Vec<Navigator>,
    restrictions: Vec<PortMap>,
}

impl Holon {
    /// A Holon on a port Holon; its active relation starts at zero (no active power).
    pub fn new(port_holon: PortHolon) -> Result<Self, HolonError> {
        let alpha = port_holon.counts.active;
        Ok(Self {
            port_holon,
            active: ActiveRelation::new(ExactRatMatrix::zero(alpha, alpha)?)?,
            pump: None,
            ports: None,
            complex: None,
            connection: None,
            interior: None,
            port_faces: None,
            navigators: Vec::new(),
            restrictions: Vec::new(),
        })
    }

    /// Declare the active relation `e_A = L f_A` on the active ports.
    pub fn with_active(mut self, relation: ActiveRelation) -> Result<Self, HolonError> {
        let alpha = self.port_holon.counts.active;
        let l = relation.relation();
        if l.rows() != alpha || l.columns() != alpha {
            return Err(HolonError::Shape {
                what: "active relation extent",
                expected: alpha,
                found: l.rows(),
            });
        }
        self.active = relation;
        Ok(self)
    }

    /// Declare a storage pump; its schedule must match the storage extent.
    pub fn with_pump(mut self, pump: Pump) -> Result<Self, HolonError> {
        if pump.schedule.extent() != self.port_holon.counts.storage {
            return Err(HolonError::Shape {
                what: "pump storage extent",
                expected: self.port_holon.counts.storage,
                found: pump.schedule.extent(),
            });
        }
        self.pump = Some(pump);
        Ok(self)
    }

    /// Name the ports; one per port of `D`.
    pub fn with_ports(mut self, ports: Vec<Port>) -> Result<Self, HolonError> {
        if ports.len() != self.port_holon.counts.total() {
            return Err(HolonError::Shape {
                what: "named ports",
                expected: self.port_holon.counts.total(),
                found: ports.len(),
            });
        }
        self.ports = Some(ports);
        Ok(self)
    }

    /// Place the Holon on a complex; an interior chain or port faces declared on an earlier
    /// complex are dropped, since they name its cells.
    pub fn with_complex(
        mut self,
        complex: CellComplex,
        connection: Option<ConnectionIncidence>,
    ) -> Self {
        self.complex = Some(complex);
        self.connection = connection;
        self.interior = None;
        self.port_faces = None;
        self
    }

    /// [definition] Declare its **oriented interior chain**: one coefficient per region (top-degree
    /// cell) of its complex (Lean `Holarchy/Join.Constituent.interior`).
    pub fn with_interior(mut self, interior: Vec<Rat>) -> Result<Self, HolonError> {
        let complex = self.complex.as_ref().ok_or(HolonError::Unsupported {
            what: "an interior chain",
            reason: "the Holon is placed on no complex",
        })?;
        let regions = complex.cells(complex.dimension());
        if interior.len() != regions {
            return Err(HolonError::Shape {
                what: "interior chain (one coefficient per region)",
                expected: regions,
                found: interior.len(),
            });
        }
        self.interior = Some(interior);
        Ok(self)
    }

    /// [definition] Declare **the face each external port sits on**: one cell of its complex one
    /// degree below the regions per external port (Lean `Holarchy/Join.Constituent.portFace`).
    pub fn with_port_faces(mut self, faces: Vec<usize>) -> Result<Self, HolonError> {
        let complex = self.complex.as_ref().ok_or(HolonError::Unsupported {
            what: "port faces",
            reason: "the Holon is placed on no complex",
        })?;
        let external = self.port_holon.counts.external;
        if faces.len() != external {
            return Err(HolonError::Shape {
                what: "port faces (one per external port)",
                expected: external,
                found: faces.len(),
            });
        }
        let cells = complex
            .dimension()
            .checked_sub(1)
            .map_or(0, |face_degree| complex.cells(face_degree));
        if let Some(face) = faces.iter().find(|face| **face >= cells) {
            return Err(HolonError::CellOutside { cell: *face, cells });
        }
        self.port_faces = Some(faces);
        Ok(self)
    }

    pub fn with_navigator(mut self, navigator: Navigator) -> Self {
        self.navigators.push(navigator);
        self
    }

    /// Declare a restriction; its source must be this Holon's ports.
    pub fn with_restriction(mut self, map: PortMap) -> Result<Self, HolonError> {
        if map.source_ports() != self.port_holon.counts.total() {
            return Err(HolonError::Shape {
                what: "restriction source ports",
                expected: self.port_holon.counts.total(),
                found: map.source_ports(),
            });
        }
        self.restrictions.push(map);
        Ok(self)
    }

    pub fn port_holon(&self) -> &PortHolon {
        &self.port_holon
    }

    pub fn active(&self) -> &ActiveRelation {
        &self.active
    }

    pub fn pump(&self) -> Option<&Pump> {
        self.pump.as_ref()
    }

    pub fn ports(&self) -> Option<&[Port]> {
        self.ports.as_deref()
    }

    pub fn complex(&self) -> Option<&CellComplex> {
        self.complex.as_ref()
    }

    pub fn connection(&self) -> Option<&ConnectionIncidence> {
        self.connection.as_ref()
    }

    /// Its oriented interior chain on the regions of its complex, when declared.
    pub fn interior(&self) -> Option<&[Rat]> {
        self.interior.as_deref()
    }

    /// The face of its complex each external port sits on, when declared.
    pub fn port_faces(&self) -> Option<&[usize]> {
        self.port_faces.as_deref()
    }

    pub fn navigators(&self) -> &[Navigator] {
        &self.navigators
    }

    pub fn restrictions(&self) -> &[PortMap] {
        &self.restrictions
    }

    /// The storage in force at a commit: the pump's schedule, or the declared form.
    pub fn storage_at(&self, commit: u64) -> &SymmetricForm {
        match &self.pump {
            Some(pump) => pump.schedule.storage_at(commit),
            None => self.port_holon.storage(),
        }
    }

    /// The element relations as a list, each on its kind.
    pub fn elements(&self) -> Vec<ElementRelation> {
        let mut out = vec![
            ElementRelation::Storage {
                form: self.port_holon.storage.clone(),
            },
            ElementRelation::Resistive(self.port_holon.resistance.clone()),
            ElementRelation::Source {
                ports: self.port_holon.counts.external,
            },
            ElementRelation::Active(self.active.clone()),
        ];
        if let Some(pump) = &self.pump {
            out.push(ElementRelation::Pump(pump.clone()));
        }
        out
    }

    /// `⟨f, L f⟩` on the active ports.
    pub fn active_power(&self, flow: &[Rat]) -> Result<Rat, HolonError> {
        self.active.power(flow)
    }

    /// The storage matrix at a commit.
    pub fn storage_matrix_at(&self, commit: u64) -> ExactRatMatrix {
        form_matrix(self.storage_at(commit))
    }

    /// `⟨f, R f⟩` on the resistive ports.
    pub fn dissipation(&self, flow: &[Rat]) -> Result<Rat, HolonError> {
        Ok(quad(self.port_holon.resistance.resistance(), flow)?)
    }
}

/// [definition] **A point on a Holon**: its storage configuration and the commit index (the
/// material's clock). Only the current point is retained.
///
/// [definition; agent-inferred] The configuration defaults to the exact storage coordinates
/// `Vec<Rat>` of the reference motion; an event chart uses the retained quotient as its
/// configuration, so the state carries no event archive in either chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HolonState<C = Vec<Rat>> {
    pub configuration: C,
    pub commit: u64,
}

impl<C> HolonState<C> {
    /// A point at a declared commit.
    pub fn at(configuration: C, commit: u64) -> Self {
        Self {
            configuration,
            commit,
        }
    }

    /// The successor point: the next configuration one commit later. When the commit clock would
    /// overflow, the configuration is returned untouched as the refusal.
    pub fn committed(&self, configuration: C) -> Result<Self, C> {
        match self.commit.checked_add(1) {
            Some(commit) => Ok(Self {
                configuration,
                commit,
            }),
            None => Err(configuration),
        }
    }
}

impl HolonState {
    pub fn new(configuration: Vec<Rat>) -> Self {
        Self {
            configuration,
            commit: 0,
        }
    }

    pub fn is_rest(&self) -> bool {
        self.configuration.iter().all(Zero::is_zero)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::{integer_matrix, ints};
    use crate::ratio::rat;

    fn one_medium(g: i64) -> PortHolon {
        PortHolon::medium(
            &ExactRatMatrix::zero(1, 1).unwrap(),
            &integer_matrix(&[&[1]]).unwrap(),
            SymmetricForm::from_integers(&[vec![g]]).unwrap(),
            &integer_matrix(&[&[0]]).unwrap(),
            false,
        )
        .unwrap()
    }

    /// `Holon/Conformance.medium_admits` and `Holon/Element.PortHolon.power_balance`.
    #[test]
    fn every_medium_motion_is_admitted_and_balances() {
        let omega = integer_matrix(&[&[0, 2], &[-2, 0]]).unwrap();
        let m = integer_matrix(&[&[1, 0], &[0, 3]]).unwrap();
        let g = SymmetricForm::from_integers(&[vec![2, 1], vec![1, 1]]).unwrap();
        let b = integer_matrix(&[&[1], &[-1]]).unwrap();
        let h = PortHolon::medium(&omega, &m, g.clone(), &b, false).unwrap();
        let q = ints(&[1, -2]);
        let u = ints(&[3]);
        let e = storage_effort(&g, &q).unwrap();
        let v = crate::ratio::linear::vector::add(
            &omega.subtract(&m).unwrap().apply(&e).unwrap(),
            &b.apply(&u).unwrap(),
        );
        let external = Bond::new(b.transpose().unwrap().apply(&e).unwrap(), u).unwrap();
        let active = Bond::zero(0);
        let balance = h.power_balance(&q, &v, &e, &external, &active).unwrap();
        assert!(balance.residual().is_zero());
        assert!(balance.dissipated > Rat::zero());
        // A velocity off the medium law is not admitted.
        let wrong = crate::ratio::linear::vector::add(&v, &ints(&[1, 0]));
        assert_eq!(
            h.power_balance(&q, &wrong, &e, &external, &active),
            Err(HolonError::NotAdmitted)
        );
    }

    /// `Holon/Conformance.two_media_witness`, `Holon/Law.storageEnergy_blocks`.
    #[test]
    fn two_media_joined_are_a_holon_with_additive_energy() {
        let holarchy = Holon::new(one_medium(2))
            .unwrap()
            .interconnect(
                &Holon::new(one_medium(3)).unwrap(),
                &crate::holarchy::Gluing::at_ports(vec![(0, 0)]).unwrap(),
            )
            .unwrap();
        let joined = holarchy.whole().port_holon();
        assert_eq!(joined.counts().external, 0);
        assert_eq!(joined.counts().storage, 2);
        assert!(joined.dirac().form().is_dirac().unwrap());
        assert_eq!(
            joined.storage_energy(&ints(&[1, 1])).unwrap(),
            integer(1) + rat(3, 2)
        );
    }
}
