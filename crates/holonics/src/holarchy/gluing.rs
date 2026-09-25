//! **The typed gluing of two Holons and the checks `interconnect` runs on it.**
//!
//! [definition] A [`Gluing`] declares only how two Holons join (Lean
//! `Holarchy/Join.JoinDeclaration`): which external ports are shared and the join law on them
//! (`f_B = −F f_A`, `e_B = E e_A`, `Holarchy/Join.joinBond`), the glued complex with a cellular
//! embedding of each Holon's own complex ([`CellGluing`], `Holarchy/Join.CellEmbedding`), and the
//! joint clock ([`JointClock`]). Everything else is read from the two Holons themselves
//! (`Holarchy/Join.Constituent`): the units of their named ports, their complexes, connections,
//! interior chains and port faces, their pumps and their navigators. The nine checks, in the order
//! of `Holarchy/Join.interconnect`, and the typed [`GluingDefect`] each returns:
//!
//! 1. **Units**: each shared port carries the same declared units on both sides
//!    ([`GluingDefect::UnitMismatch`]).
//! 2. **Interface power**: the join cancels the interface power `⟨e, (1 − EᵀF) f⟩` exactly when
//!    `EᵀF = 1` (`Holarchy/Join.interfacePower_eq`, `interfacePower_cancels_iff`); otherwise a
//!    shared bond with nonzero interface power is returned ([`GluingDefect::UncancelledPower`]).
//! 3. **Commuting**: each embedding commutes with the glued boundary and the Holon's own
//!    (connection-valued on edges when it carries a connection), `∂'_k m_k = m_(k−1) ∂_k`
//!    ([`GluingDefect::NonCommutingCells`]).
//! 4. **Injective**: each embedding sends distinct cells to distinct cells
//!    ([`GluingDefect::DegenerateCells`]).
//! 5. **Cover**: the two images cover the glued complex ([`GluingDefect::UncoveredCells`]).
//! 6. **Identified**: each shared port's two faces land on one glued face
//!    ([`GluingDefect::UnidentifiedSharedFace`]).
//! 7. **Overlap**: the images share no region, and share a face only where a shared port's two
//!    faces land ([`GluingDefect::StrayOverlap`]).
//! 8. **Cancellation**: each shared face enters the two Holons' pushed boundaries of their
//!    interiors with opposite coefficients, so it is interior to the whole
//!    ([`GluingDefect::SharedFaceUncancelled`]).
//! 9. **Pumps**: each Holon's pump turns a whole number of times per turn of the joint clock,
//!    `rate_p = k_p · ω` with `k_p ∈ ℕ` (`Holarchy/Join.OnJointClock`, `PumpsOnClock`)
//!    ([`GluingDefect::IncompatibleClocks`]).
//!
//! A declaration that does not fit the two Holons at all (a shared port outside a Holon, a map of
//! the wrong shape, a Holon carrying a complex that no map places, or a Holon on a glued complex
//! without its interior or port faces) is a [`GluingDefect::Malformed`] refusal: in Lean it is a
//! type error. So is a map that is not cell-to-cell with a unit gauge ([`CellularMap::new`]); in
//! particular a zero map is no cellular embedding (`Holarchy/Join.CellEmbedding.m₂_ne_zero`).
//!
//! [definition; agent-inferred] The Rust complex has any number of degrees `0..=d`; the checks
//! read Lean's three grades as the regions `d`, the faces `d − 1` and the cells below, where Lean's
//! vertices `C₀` stand. As in Lean, cells below the faces may be shared freely. A pump's rate is
//! read from its own clock (Lean reads it from the navigator driving it,
//! `Holarchy/Join.Constituent.pumpRate`); a Holon carries at most one pump.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use thiserror::Error;

use crate::geometry::complex::{CellComplex, ConnectionIncidence};
use crate::holarchy::Side;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{Pump, PumpSchedule, ResistiveRelation};
use crate::holon::port::{Bond, PortUnits};
use crate::holon::{Holon, HolonError, PortCounts, PortHolon};
use crate::navigator::Clock;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{at, block_diagonal, from_blocks};

/// [definition] **The typed gluing defect** (Lean `Holarchy/Join.GluingDefect`): the first failed
/// check with its witness, read from the two Holons, or a declaration that does not fit them.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum GluingDefect {
    /// A shared port whose two sides declare different units (`unitMismatch`). A Holon that names
    /// no ports declares no units, so it agrees only with another undeclared side.
    #[error("shared port {shared} declares different units on its two sides")]
    UnitMismatch {
        shared: usize,
        left: Option<PortUnits>,
        right: Option<PortUnits>,
    },
    /// A shared bond whose interface power the declared join does not cancel
    /// (`uncancelledPower`, from `exists_interfacePower_ne_zero`).
    #[error("the join does not cancel the interface power: {power} on a shared bond")]
    UncancelledPower { bond: Bond, power: Rat },
    /// A Holon whose embedding does not commute with the boundaries at `degree`
    /// (`nonCommutingCells`): `∂'_k m_k ≠ m_(k−1) ∂_k`.
    #[error("the {side:?} embedding does not commute with the boundaries at degree {degree}")]
    NonCommutingCells { side: Side, degree: usize },
    /// A Holon whose embedding merges two of its cells of one degree (`degenerateCells`).
    #[error("the {side:?} embedding merges cells {cells:?} of degree {degree}")]
    DegenerateCells {
        side: Side,
        degree: usize,
        cells: (usize, usize),
    },
    /// A glued cell that belongs to neither Holon (`uncoveredCells`).
    #[error("glued cell {cell} of degree {degree} belongs to neither constituent")]
    UncoveredCells { degree: usize, cell: usize },
    /// A shared port whose two faces land on two glued faces (`unidentifiedSharedFace`).
    #[error(
        "shared port {shared} sits on glued face {left} from the left and {right} from the right"
    )]
    UnidentifiedSharedFace {
        shared: usize,
        left: usize,
        right: usize,
    },
    /// The two images meet on a region, or on a face where no shared port's faces land
    /// (`strayOverlap`).
    #[error(
        "the two constituents meet on glued cell {cell} of degree {degree}, which no shared port declares"
    )]
    StrayOverlap { degree: usize, cell: usize },
    /// A shared port's face on which the two pushed boundary coefficients do not cancel, so it is
    /// not interior to the whole (`sharedFaceUncancelled`).
    #[error(
        "shared port {shared}'s face {face} is not interior to the whole: coefficients {left} and {right}"
    )]
    SharedFaceUncancelled {
        shared: usize,
        face: usize,
        left: Rat,
        right: Rat,
    },
    /// A Holon's pump that does not turn a whole number of times per joint turn
    /// (`incompatibleClocks`): its rate and the joint rate, which may be undeclared.
    #[error(
        "the {side:?} pump turns at {rate} per unit duration, not a whole multiple of the joint rate"
    )]
    IncompatibleClocks {
        side: Side,
        rate: Rat,
        joint_rate: Option<Rat>,
    },
    /// The declaration does not fit the two Holons (a type error in Lean).
    #[error("the gluing does not fit the Holons: {0}")]
    Malformed(HolonError),
}

impl From<GluingDefect> for HolonError {
    /// A malformed declaration is the Holon refusal it carries; a gluing defect is boxed.
    fn from(defect: GluingDefect) -> Self {
        match defect {
            GluingDefect::Malformed(error) => error,
            defect => HolonError::Gluing(Box::new(defect)),
        }
    }
}

/// [definition] **A cellular embedding** grade by grade (Lean `Holarchy/Join.CellEmbedding`):
/// `m_k : C_k(K) → C_k(K')`, one `glued.cells(k) × own.cells(k)` matrix per degree, each column one
/// unit entry: the cell it lands on and its gauge (an orientation sign, or the value of an oriented
/// connection transport).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellularMap {
    degrees: Vec<ExactRatMatrix>,
    images: Vec<Vec<usize>>,
}

impl CellularMap {
    /// Refuses a column that is not exactly one nonzero entry: such a matrix sends a cell to no
    /// glued cell or to several, and is no cellular embedding. A zero map on a nonempty complex is
    /// refused here (`CellEmbedding.m₂_ne_zero`) rather than commuting vacuously.
    pub fn new(degrees: Vec<ExactRatMatrix>) -> Result<Self, HolonError> {
        let mut images = Vec::with_capacity(degrees.len());
        for (degree, map) in degrees.iter().enumerate() {
            let mut image = Vec::with_capacity(map.columns());
            for cell in 0..map.columns() {
                let mut hits = (0..map.rows()).filter(|row| !at(map, *row, cell).is_zero());
                match (hits.next(), hits.next()) {
                    (Some(row), None) => image.push(row),
                    _ => return Err(HolonError::NotACellularMap { degree, cell }),
                }
            }
            images.push(image);
        }
        Ok(Self { degrees, images })
    }

    /// `m_k`.
    pub fn degree(&self, degree: usize) -> Option<&ExactRatMatrix> {
        self.degrees.get(degree)
    }

    pub fn degrees(&self) -> &[ExactRatMatrix] {
        &self.degrees
    }

    /// The glued cell each own cell of `degree` lands on (Lean `CellEmbedding.c₀`, `c₁`, `c₂`).
    pub fn image(&self, degree: usize) -> &[usize] {
        self.images.get(degree).map_or(&[], Vec::as_slice)
    }
}

/// [definition] **The cellular gluing**: the glued complex (with its connection, when its edges
/// carry one) and each Holon's cellular embedding into it. The interiors and port faces are the
/// Holons' own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellGluing {
    glued: CellComplex,
    connection: Option<ConnectionIncidence>,
    left: CellularMap,
    right: CellularMap,
}

impl CellGluing {
    pub fn new(
        glued: CellComplex,
        connection: Option<ConnectionIncidence>,
        maps: (CellularMap, CellularMap),
    ) -> Self {
        Self {
            glued,
            connection,
            left: maps.0,
            right: maps.1,
        }
    }

    pub fn glued(&self) -> &CellComplex {
        &self.glued
    }

    pub fn connection(&self) -> Option<&ConnectionIncidence> {
        self.connection.as_ref()
    }

    pub fn map(&self, side: Side) -> &CellularMap {
        match side {
            Side::Left => &self.left,
            Side::Right => &self.right,
        }
    }

    /// The region degree: the top degree of the glued complex.
    pub fn region_degree(&self) -> usize {
        self.glued.dimension()
    }

    /// `∂'_k` of the glued complex, connection-valued on edges when a connection is declared.
    pub(crate) fn glued_boundary(&self, degree: usize) -> Result<ExactRatMatrix, HolonError> {
        boundary(Some(&self.glued), self.connection.as_ref(), degree)
    }

    pub(crate) fn map_at(&self, side: Side, degree: usize) -> Result<&ExactRatMatrix, HolonError> {
        self.map(side).degree(degree).ok_or(HolonError::Shape {
            what: "cellular map degree",
            expected: degree + 1,
            found: self.map(side).degrees().len(),
        })
    }

    /// A Holon's interior pushed into the glued regions, `m_d c` (Lean `m₂ *ᵥ interior`).
    pub(crate) fn pushed_interior(
        &self,
        side: Side,
        holon: &Holon,
    ) -> Result<Vec<Rat>, HolonError> {
        Ok(self
            .map_at(side, self.region_degree())?
            .apply(holon_interior(holon)?)?)
    }

    /// A Holon's own boundary of its interior pushed onto the glued faces, `m_(d−1) ∂_d c`.
    pub(crate) fn pushed_boundary(
        &self,
        side: Side,
        holon: &Holon,
    ) -> Result<Vec<Rat>, HolonError> {
        let d = self.region_degree();
        let own =
            boundary(holon.complex(), holon.connection(), d)?.apply(holon_interior(holon)?)?;
        Ok(self.map_at(side, d.saturating_sub(1))?.apply(&own)?)
    }
}

/// A Holon's interior chain, required on a glued complex.
pub(crate) fn holon_interior(holon: &Holon) -> Result<&[Rat], HolonError> {
    holon.interior().ok_or(HolonError::Unsupported {
        what: "a constituent on a glued complex",
        reason: "it declares no interior chain",
    })
}

/// The cells of a Holon's own complex at a degree; a Holon with no complex has none.
pub(crate) fn own_cells(complex: Option<&CellComplex>, degree: usize) -> usize {
    complex.map_or(0, |complex| complex.cells(degree))
}

/// `∂_k` as a `cells(k−1) × cells(k)` matrix: the declared boundary, connection-valued on edges
/// (`d_Aᵀ`) when a connection is carried, and zero where the complex has no such degree.
pub(crate) fn boundary(
    complex: Option<&CellComplex>,
    connection: Option<&ConnectionIncidence>,
    degree: usize,
) -> Result<ExactRatMatrix, HolonError> {
    let (rows, columns) = (
        own_cells(complex, degree.saturating_sub(1)),
        own_cells(complex, degree),
    );
    if degree == 1
        && let Some(connection) = connection
    {
        let charted = connection.matrix()?.transpose()?;
        if charted.rows() != rows || charted.columns() != columns {
            return Err(HolonError::Shape {
                what: "connection-valued boundary",
                expected: rows * columns,
                found: charted.rows() * charted.columns(),
            });
        }
        return Ok(charted);
    }
    match complex.and_then(|complex| complex.boundary(degree)) {
        Some(boundary) => Ok(boundary.clone()),
        None => Ok(ExactRatMatrix::zero(rows, columns)?),
    }
}

/// [definition] **The joint clock** of the Holarchy (Lean `JoinDeclaration.jointRate`): a declared
/// clock whose turn rate `ω` every pump must be a whole multiple of.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointClock {
    clock: Clock,
}

impl JointClock {
    pub fn new(clock: Clock) -> Self {
        Self { clock }
    }

    pub fn clock(&self) -> &Clock {
        &self.clock
    }

    /// The joint rate `ω`: joint turns per unit duration.
    pub fn rate(&self) -> Rat {
        turn_rate(&self.clock)
    }

    /// [definition] **The whole multiple** `k ∈ ℕ` with `rate = k · ω`, when there is one (Lean
    /// `OnJointClock`). The joint rate is positive, so `k` is `rate/ω` when that is a natural.
    pub fn multiple(&self, rate: &Rat) -> Option<BigUint> {
        let quotient = rate / self.rate();
        quotient
            .is_integer()
            .then(|| quotient.to_integer().to_biguint())
            .flatten()
    }
}

/// [definition] **The turn rate of a clock**: turns per unit duration, `1 / (h · Π radices)`. A turn
/// is one jump (a section crossing); an unwound clock jumps at every tick. The step is positive by
/// construction, so the rate is a unit of ℚ, never a degenerate ratio. Lean reads a navigator's
/// rate as `Holarchy/Join.NavigatorClock.rate`.
pub(crate) fn turn_rate(clock: &Clock) -> Rat {
    Rat::one() / (clock.step() * Rat::from_integer(BigInt::from(clock.period())))
}

/// [definition] **The gluing declaration** of two Holons (Lean `Holarchy/Join.JoinDeclaration`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gluing {
    shared: Vec<(usize, usize)>,
    flow_gain: ExactRatMatrix,
    effort_gain: ExactRatMatrix,
    cells: Option<CellGluing>,
    joint_clock: Option<JointClock>,
}

impl Gluing {
    /// The equal-effort, opposite-flow join `F = E = 1` (Lean `Holarchy/Join.gainLink_one`) at the
    /// listed shared external ports `(left, right)`, with no cells and no joint clock.
    pub fn at_ports(shared: Vec<(usize, usize)>) -> Result<Self, HolonError> {
        let identity = ExactRatMatrix::identity(shared.len())?;
        Ok(Self {
            shared,
            flow_gain: identity.clone(),
            effort_gain: identity,
            cells: None,
            joint_clock: None,
        })
    }

    /// Declare the join law's gains `F` and `E`, each `t × t` for `t` shared ports.
    pub fn with_gains(
        mut self,
        flow_gain: ExactRatMatrix,
        effort_gain: ExactRatMatrix,
    ) -> Result<Self, HolonError> {
        let t = self.shared.len();
        for gain in [&flow_gain, &effort_gain] {
            if gain.rows() != t || gain.columns() != t {
                return Err(HolonError::Shape {
                    what: "join gain (shared × shared)",
                    expected: t * t,
                    found: gain.rows() * gain.columns(),
                });
            }
        }
        self.flow_gain = flow_gain;
        self.effort_gain = effort_gain;
        Ok(self)
    }

    pub fn with_cells(mut self, cells: CellGluing) -> Self {
        self.cells = Some(cells);
        self
    }

    pub fn with_joint_clock(mut self, clock: JointClock) -> Self {
        self.joint_clock = Some(clock);
        self
    }

    pub fn shared(&self) -> &[(usize, usize)] {
        &self.shared
    }

    pub fn flow_gain(&self) -> &ExactRatMatrix {
        &self.flow_gain
    }

    pub fn effort_gain(&self) -> &ExactRatMatrix {
        &self.effort_gain
    }

    pub fn cells(&self) -> Option<&CellGluing> {
        self.cells.as_ref()
    }

    pub fn joint_clock(&self) -> Option<&JointClock> {
        self.joint_clock.as_ref()
    }

    /// [definition] **The shared bond seen by the right Holon** when the left carries `q`:
    /// `f_B = −F f_A`, `e_B = E e_A` (Lean `Holarchy/Join.joinBond`).
    pub fn join_bond(&self, bond: &Bond) -> Result<Bond, HolonError> {
        Bond::new(
            crate::ratio::linear::vector::neg(&self.flow_gain.apply(bond.flow())?),
            self.effort_gain.apply(bond.effort())?,
        )
    }

    /// [definition] **The interface power** of a shared bond: the power into the left Holon at the
    /// shared ports plus the power into the right one (Lean `Holarchy/Join.interfacePower`).
    pub fn interface_power(&self, bond: &Bond) -> Result<Rat, HolonError> {
        Ok(bond.power() + self.join_bond(bond)?.power())
    }

    /// Check 2: `EᵀF = 1`, or the shared bond `(f = δ_j, e = δ_i)` at an entry where
    /// `(1 − EᵀF)_(ij) ≠ 0`, whose interface power is that entry (`interfacePower_eq`).
    pub(crate) fn check_power(&self) -> Result<(), GluingDefect> {
        let t = self.shared.len();
        let product = self
            .effort_gain
            .transpose()
            .and_then(|e| e.multiply(&self.flow_gain))
            .map_err(|error| GluingDefect::Malformed(error.into()))?;
        for i in 0..t {
            for j in 0..t {
                let expected = if i == j { Rat::one() } else { Rat::zero() };
                if at(&product, i, j) != expected {
                    let mut flow = vec![Rat::zero(); t];
                    let mut effort = vec![Rat::zero(); t];
                    flow[j] = Rat::one();
                    effort[i] = Rat::one();
                    let bond = Bond::new(flow, effort).map_err(GluingDefect::Malformed)?;
                    let power = self
                        .interface_power(&bond)
                        .map_err(GluingDefect::Malformed)?;
                    return Err(GluingDefect::UncancelledPower { bond, power });
                }
            }
        }
        Ok(())
    }
}

/// Where a constituent port's bond comes from: a port of the whole, or a shared bond.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Slot {
    Whole(usize),
    Shared(usize),
}

/// [definition] Which constituent port each port of the whole comes from, and where it sits
/// before the kinds are merged. The whole's ports are merged kind by kind, left before right,
/// with the shared external ports removed (Lean `Holon/Law.mergeKinds`); the provenance is the
/// sum type's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Layout {
    /// Whole port `i` is port `provenance[i].1` of constituent `provenance[i].0`.
    pub(crate) provenance: Vec<(Side, usize)>,
    /// Each constituent's external ports that stay external, in order.
    left_free: Vec<usize>,
    right_free: Vec<usize>,
    /// Where each constituent port's bond comes from.
    pub(crate) left_slots: Vec<Slot>,
    pub(crate) right_slots: Vec<Slot>,
    left_counts: PortCounts,
    right_counts: PortCounts,
    shared: Vec<(usize, usize)>,
}

impl Layout {
    pub(crate) fn new(
        a: PortCounts,
        b: PortCounts,
        shared: &[(usize, usize)],
    ) -> Result<Self, HolonError> {
        for (index, (i, j)) in shared.iter().enumerate() {
            if *i >= a.external {
                return Err(HolonError::PortOutside {
                    port: *i,
                    ports: a.external,
                });
            }
            if *j >= b.external {
                return Err(HolonError::PortOutside {
                    port: *j,
                    ports: b.external,
                });
            }
            if shared[..index].iter().any(|(i2, _)| i2 == i) {
                return Err(HolonError::PortJoinedTwice { port: *i });
            }
            if shared[..index].iter().any(|(_, j2)| j2 == j) {
                return Err(HolonError::PortJoinedTwice { port: *j });
            }
        }
        let left_free: Vec<usize> = (0..a.external)
            .filter(|e| !shared.iter().any(|(i, _)| i == e))
            .collect();
        let right_free: Vec<usize> = (0..b.external)
            .filter(|e| !shared.iter().any(|(_, j)| j == e))
            .collect();
        let mut provenance = Vec::new();
        let kind = |side: Side, offset: usize, count: usize| -> Vec<(Side, usize)> {
            (0..count).map(|k| (side, offset + k)).collect()
        };
        provenance.extend(kind(Side::Left, 0, a.storage));
        provenance.extend(kind(Side::Right, 0, b.storage));
        provenance.extend(kind(Side::Left, a.resistive_offset(), a.resistive));
        provenance.extend(kind(Side::Right, b.resistive_offset(), b.resistive));
        provenance.extend(
            left_free
                .iter()
                .map(|e| (Side::Left, a.external_offset() + e)),
        );
        provenance.extend(
            right_free
                .iter()
                .map(|e| (Side::Right, b.external_offset() + e)),
        );
        provenance.extend(kind(Side::Left, a.active_offset(), a.active));
        provenance.extend(kind(Side::Right, b.active_offset(), b.active));
        let mut left_slots = vec![Slot::Shared(0); a.total()];
        let mut right_slots = vec![Slot::Shared(0); b.total()];
        for (k, (i, j)) in shared.iter().enumerate() {
            left_slots[a.external_offset() + i] = Slot::Shared(k);
            right_slots[b.external_offset() + j] = Slot::Shared(k);
        }
        for (whole, (side, port)) in provenance.iter().enumerate() {
            match side {
                Side::Left => left_slots[*port] = Slot::Whole(whole),
                Side::Right => right_slots[*port] = Slot::Whole(whole),
            }
        }
        Ok(Self {
            provenance,
            left_free,
            right_free,
            left_slots,
            right_slots,
            left_counts: a,
            right_counts: b,
            shared: shared.to_vec(),
        })
    }

    pub(crate) fn counts(&self) -> PortCounts {
        let (a, b) = (self.left_counts, self.right_counts);
        PortCounts {
            storage: a.storage + b.storage,
            resistive: a.resistive + b.resistive,
            external: self.left_free.len() + self.right_free.len(),
            active: a.active + b.active,
        }
    }

    /// The shared ports' global indices in the side-by-side pair: the left's, then the right's.
    pub(crate) fn internal(&self) -> Vec<usize> {
        let (a, b) = (self.left_counts, self.right_counts);
        self.shared
            .iter()
            .map(|(i, _)| a.external_offset() + i)
            .chain(
                self.shared
                    .iter()
                    .map(|(_, j)| a.total() + b.external_offset() + j),
            )
            .collect()
    }

    /// Where each whole port sits among the ports a composition keeps: the left's unshared ports
    /// in order, then the right's.
    pub(crate) fn composed_order(&self) -> Vec<usize> {
        let left_kept: Vec<usize> = (0..self.left_counts.total())
            .filter(|p| matches!(self.left_slots[*p], Slot::Whole(_)))
            .collect();
        let right_kept: Vec<usize> = (0..self.right_counts.total())
            .filter(|p| matches!(self.right_slots[*p], Slot::Whole(_)))
            .collect();
        self.provenance
            .iter()
            .map(|(side, port)| {
                let (kept, offset) = match side {
                    Side::Left => (&left_kept, 0),
                    Side::Right => (&right_kept, left_kept.len()),
                };
                offset
                    + kept.iter().position(|p| p == port).expect(
                        "every whole port is an unshared port its constituent keeps (`Layout::new`)",
                    )
            })
            .collect()
    }
}

/// [definition] **The gain link** on two copies of the shared bond (Lean
/// `Holarchy/Join.gainLink`): the graph of `q ↦ (−F q_f, E q_e)`, in kernel form
/// `f_B + F f_A = 0`, `e_B − E e_A = 0`. It is Dirac exactly when `EᵀF = 1`
/// (`gainLink_isDirac`); the kernel-form test certifies it.
fn gain_link(
    flow_gain: &ExactRatMatrix,
    effort_gain: &ExactRatMatrix,
) -> Result<DiracStructure, HolonError> {
    let t = flow_gain.rows();
    let identity = ExactRatMatrix::identity(t)?;
    let zero = ExactRatMatrix::zero(t, t)?;
    let flow = from_blocks(flow_gain, &identity, &zero, &zero)?;
    let effort = from_blocks(&zero, &zero, &effort_gain.scaled(&-Rat::one()), &identity)?;
    DiracStructure::kernel_form(&flow, &effort)
}

/// [definition] **The joined port Holon** (Lean `Holarchy/Join.joinHolon`): both structures side
/// by side (`pairedD`), composed with the gain link at the shared ports (`compose`), the kinds
/// merged; block storage and resistance. Dirac when `EᵀF = 1` (`joinD_isDirac`, re-certified by
/// every composition); at `F = E = 1` it is the Dirac interconnection (`joinHolon_one`).
pub(crate) fn join_port_holons(
    left: &PortHolon,
    right: &PortHolon,
    gluing: &Gluing,
    layout: &Layout,
) -> Result<PortHolon, HolonError> {
    let paired = left.dirac().interconnect(right.dirac(), &[])?;
    let composed = paired.compose(
        &gain_link(&gluing.flow_gain, &gluing.effort_gain)?,
        &layout.internal(),
    )?;
    let dirac = composed.relabel(&layout.composed_order())?;
    PortHolon::new(
        dirac,
        layout.counts(),
        left.storage().direct_sum(right.storage()),
        ResistiveRelation::new(block_diagonal(
            left.resistance().resistance(),
            right.resistance().resistance(),
        )?)?,
    )
}

/// The declared units of a Holon's port, when the Holon names its ports.
fn port_units(holon: &Holon, port: usize) -> Option<PortUnits> {
    holon
        .ports()
        .and_then(|ports| ports.get(port))
        .map(|port| port.units.clone())
}

/// Check 1: each shared port's two sides declare the same units.
pub(crate) fn check_units(
    left: &Holon,
    right: &Holon,
    gluing: &Gluing,
) -> Result<(), GluingDefect> {
    let (a, b) = (left.port_holon().counts(), right.port_holon().counts());
    for (index, (i, j)) in gluing.shared.iter().enumerate() {
        let left_units = port_units(left, a.external_offset() + i);
        let right_units = port_units(right, b.external_offset() + j);
        if left_units != right_units {
            return Err(GluingDefect::UnitMismatch {
                shared: index,
                left: left_units,
                right: right_units,
            });
        }
    }
    Ok(())
}

/// The shapes a cellular gluing must have against the two Holons' own complexes, interiors and
/// port faces; a mismatch is a malformed declaration (a type error in Lean).
pub(crate) fn check_cell_shapes(
    left: &Holon,
    right: &Holon,
    gluing: &Gluing,
) -> Result<(), HolonError> {
    let Some(cells) = &gluing.cells else {
        if left.complex().is_some() || right.complex().is_some() {
            return Err(HolonError::Unsupported {
                what: "a gluing without cells",
                reason: "a constituent carries a complex that no cellular map places",
            });
        }
        return Ok(());
    };
    let d = cells.region_degree();
    for (side, holon) in [(Side::Left, left), (Side::Right, right)] {
        let complex = holon.complex().ok_or(HolonError::Unsupported {
            what: "a constituent on a glued complex",
            reason: "it is placed on no complex of its own",
        })?;
        if complex.dimension() != d {
            return Err(HolonError::Shape {
                what: "constituent complex dimension (the glued dimension)",
                expected: d,
                found: complex.dimension(),
            });
        }
        holon_interior(holon)?;
        if holon.port_faces().is_none() && holon.port_holon().counts().external > 0 {
            return Err(HolonError::Unsupported {
                what: "a constituent on a glued complex",
                reason: "it declares no face for its external ports",
            });
        }
        let map = cells.map(side);
        if map.degrees().len() != d + 1 {
            return Err(HolonError::Shape {
                what: "cellular map degrees",
                expected: d + 1,
                found: map.degrees().len(),
            });
        }
        for (k, m) in map.degrees().iter().enumerate() {
            if m.rows() != cells.glued.cells(k) || m.columns() != complex.cells(k) {
                return Err(HolonError::Shape {
                    what: "cellular map shape (glued × own cells)",
                    expected: cells.glued.cells(k) * complex.cells(k),
                    found: m.rows() * m.columns(),
                });
            }
        }
    }
    Ok(())
}

/// The two own cells of one degree an embedding sends to one glued cell, if any.
fn merged(image: &[usize]) -> Option<(usize, usize)> {
    (0..image.len()).find_map(|first| {
        (first + 1..image.len())
            .find(|second| image[*second] == image[first])
            .map(|second| (first, second))
    })
}

/// Checks 3 to 8, in Lean's order: commuting, injective, cover, identified shared faces, overlap
/// only there, and each shared face cancelled.
pub(crate) fn check_cells(
    left: &Holon,
    right: &Holon,
    gluing: &Gluing,
) -> Result<(), GluingDefect> {
    let Some(cells) = &gluing.cells else {
        return Ok(());
    };
    let malformed = GluingDefect::Malformed;
    let d = cells.region_degree();
    let sides = [(Side::Left, left), (Side::Right, right)];
    // 3. Each embedding commutes with both boundaries.
    for (side, holon) in sides {
        for k in 1..=d {
            let glued = cells.glued_boundary(k).map_err(malformed)?;
            let own = boundary(holon.complex(), holon.connection(), k).map_err(malformed)?;
            let lhs = glued
                .multiply(cells.map_at(side, k).map_err(malformed)?)
                .map_err(|error| malformed(error.into()))?;
            let rhs = cells
                .map_at(side, k - 1)
                .map_err(malformed)?
                .multiply(&own)
                .map_err(|error| malformed(error.into()))?;
            if lhs != rhs {
                return Err(GluingDefect::NonCommutingCells { side, degree: k });
            }
        }
    }
    // 4. Each embedding is injective on the cells of every degree.
    for (side, _) in sides {
        for k in 0..=d {
            if let Some(pair) = merged(cells.map(side).image(k)) {
                return Err(GluingDefect::DegenerateCells {
                    side,
                    degree: k,
                    cells: pair,
                });
            }
        }
    }
    let reached = |side: Side, k: usize, cell: usize| cells.map(side).image(k).contains(&cell);
    // 5. The two images cover the glued complex.
    for k in 0..=d {
        for cell in 0..cells.glued.cells(k) {
            if !reached(Side::Left, k, cell) && !reached(Side::Right, k, cell) {
                return Err(GluingDefect::UncoveredCells { degree: k, cell });
            }
        }
    }
    let faces = |holon: &Holon| holon.port_faces().unwrap_or_default().to_vec();
    let (left_faces, right_faces) = (faces(left), faces(right));
    let face_degree = d.saturating_sub(1);
    let glued_face = |side: Side, own: usize| cells.map(side).image(face_degree)[own];
    // 6. Each shared port's two faces land on one glued face.
    for (shared, (i, j)) in gluing.shared.iter().enumerate() {
        let (l, r) = (
            glued_face(Side::Left, left_faces[*i]),
            glued_face(Side::Right, right_faces[*j]),
        );
        if l != r {
            return Err(GluingDefect::UnidentifiedSharedFace {
                shared,
                left: l,
                right: r,
            });
        }
    }
    // 7. No shared region; a shared face only where a shared port's two faces land.
    for cell in 0..cells.glued.cells(d) {
        if reached(Side::Left, d, cell) && reached(Side::Right, d, cell) {
            return Err(GluingDefect::StrayOverlap { degree: d, cell });
        }
    }
    if d > 0 {
        let (left_image, right_image) = (
            cells.map(Side::Left).image(face_degree),
            cells.map(Side::Right).image(face_degree),
        );
        for (i, cell) in left_image.iter().enumerate() {
            if let Some(j) = right_image.iter().position(|other| other == cell) {
                let declared = gluing
                    .shared
                    .iter()
                    .any(|(p, q)| left_faces[*p] == i && right_faces[*q] == j);
                if !declared {
                    return Err(GluingDefect::StrayOverlap {
                        degree: face_degree,
                        cell: *cell,
                    });
                }
            }
        }
    }
    // 8. Each shared face enters the two pushed boundaries with opposite coefficients.
    if d > 0 && !gluing.shared.is_empty() {
        let pushed = |side: Side, holon: &Holon| {
            cells
                .pushed_boundary(side, holon)
                .map_err(GluingDefect::Malformed)
        };
        let (left_boundary, right_boundary) =
            (pushed(Side::Left, left)?, pushed(Side::Right, right)?);
        for (shared, (i, _)) in gluing.shared.iter().enumerate() {
            let face = glued_face(Side::Left, left_faces[*i]);
            let (l, r) = (&left_boundary[face], &right_boundary[face]);
            if !(l + r).is_zero() {
                return Err(GluingDefect::SharedFaceUncancelled {
                    shared,
                    face,
                    left: l.clone(),
                    right: r.clone(),
                });
            }
        }
    }
    Ok(())
}

/// Check 9: each Holon's pump turns a whole number `k ∈ ℕ` of times per joint turn,
/// `rate_p = k · ω` (Lean `PumpsOnClock`).
pub(crate) fn check_clocks(
    left: &Holon,
    right: &Holon,
    gluing: &Gluing,
) -> Result<(), GluingDefect> {
    for (side, holon) in [(Side::Left, left), (Side::Right, right)] {
        let Some(pump) = holon.pump() else {
            continue;
        };
        let rate = turn_rate(&pump.clock);
        let joint = gluing.joint_clock.as_ref();
        if joint.and_then(|joint| joint.multiple(&rate)).is_none() {
            return Err(GluingDefect::IncompatibleClocks {
                side,
                rate,
                joint_rate: joint.map(JointClock::rate),
            });
        }
    }
    Ok(())
}

/// The whole's pump: when either Holon pumps, the storage in force at every commit is the block of
/// the two Holons' storage in force, on the joint clock.
pub(crate) fn joint_pump(
    left: &Holon,
    right: &Holon,
    gluing: &Gluing,
) -> Result<Option<Pump>, HolonError> {
    if left.pump().is_none() && right.pump().is_none() {
        return Ok(None);
    }
    let Some(joint) = &gluing.joint_clock else {
        return Err(HolonError::Unsupported {
            what: "joining pumped Holons",
            reason: "no joint clock is declared",
        });
    };
    let period = |holon: &Holon| holon.pump().map_or(1, |pump| pump.schedule.period());
    let (p, q) = (period(left), period(right));
    let (mut x, mut y) = (p, q);
    while y != 0 {
        (x, y) = (y, x % y);
    }
    let joint_period = p / x * q;
    let forms = (0..joint_period as u64)
        .map(|commit| left.storage_at(commit).direct_sum(right.storage_at(commit)))
        .collect();
    Ok(Some(Pump {
        schedule: PumpSchedule::new(forms)?,
        clock: joint.clock.clone(),
    }))
}
