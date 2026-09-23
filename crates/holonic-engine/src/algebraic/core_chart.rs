//! **The engine's incidence complexes as the core complex `K`** (plan phase 4).
//!
//! [definition] [`GradedCausalComplex`] is the engine's source presentation of an oriented complex:
//! named, caused cells whose boundary coefficients are pairs of occurrence counts. The core
//! [`CellComplex`] is its incidence alone: cell counts per degree and exact boundary matrices with
//! `∂∘∂ = 0` validated. [`CoreCellChart`] is the reading of the first as the second, carrying the
//! cell identities degree by degree so every cochain the engine names can be placed on the core
//! complex and read back. The chart takes the **group completion** of each coefficient
//! (`ComparativeMultiplicity::difference`), which is what a boundary *map* means; the pair of arms,
//! the names and the source events stay on the engine presentation and are not in the core. `∂∘∂ = 0`
//! is carried: the engine validated `difference_is_zero` at every founding, and the core re-checks
//! it as a matrix identity when the chart is built (`Holon/Complex.lean::connectionIncidence` is the
//! graph case; the Kirchhoff structure of the chart's `d₀` is `Holon/Dirac.lean::kirchhoff`).
//!
//! [definition] [`GraphChart`] is the same reading for the engine's graph-shaped complexes, whose
//! cells are typed node and branch identities rather than causal cells (`DiffusionComplex`,
//! `DiscreteCurrentComplex`, `HingeTransportNetwork`): `∂₁` carries `−1` at each branch's source and
//! `+1` at its target ([`CellComplex::graph`]), and a scalar edge transport makes it the core
//! [`ConnectionIncidence`].
//!
//! [definition; agent-inferred] The engine types keep their fields and wire formats: the core
//! complex is `Serialize` only, so no remounted engine value mints an unchecked core object, and a
//! chart is always rebuilt from the engine value through the core constructor. Each engine complex
//! that carries incidence publishes a `core_chart`/`graph_chart` view; the disposition of every
//! `*Complex` type is recorded in
//! `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md` (phase 4).

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use holonic_core::complex::{CellComplex, ConnectionIncidence};
use holonic_core::holon::HolonError;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use thiserror::Error;

use super::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::EventId;
use crate::exact_linear::ExactRatMatrix;

/// Why an engine complex could not be read as a core complex, or a core complex as an engine one.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CoreChartRefusal {
    /// The core refused (shape, `∂∘∂ ≠ 0`, a non-graph edge, a zero transport). Boxed: the core's
    /// refusals carry exact witnesses.
    #[error(transparent)]
    Holon(Box<HolonError>),
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    /// A core boundary coefficient that is not an integer has no occurrence-count reading.
    #[error("the core boundary ∂_{degree} carries a non-integral coefficient at ({row}, {column})")]
    NonIntegralIncidence {
        degree: usize,
        row: usize,
        column: usize,
    },
    /// An edge names an endpoint the chart does not carry.
    #[error("edge {edge} names an endpoint outside the chart's vertices")]
    EndpointOutside { edge: usize },
    /// A vertex or edge identity occurs twice.
    #[error("the chart's {what} repeat an identity")]
    RepeatedIdentity { what: &'static str },
    /// The graph-shaped complex carries an edge its own law reads differently from a core cell.
    #[error("edge {edge} is not a core cell of this complex: {reason}")]
    NotACoreCell { edge: usize, reason: &'static str },
    /// A transport that is not a scalar dilation `t ↦ λ t`; the core connection is `ℚ^×`-valued.
    #[error(
        "transport {edge} is not a scalar dilation; the core connection carries only ℚ^× values"
    )]
    NotAScalarTransport { edge: usize },
}

impl From<HolonError> for CoreChartRefusal {
    fn from(error: HolonError) -> Self {
        Self::Holon(Box::new(error))
    }
}

impl From<crate::exact_linear::ExactLinearError> for CoreChartRefusal {
    fn from(error: crate::exact_linear::ExactLinearError) -> Self {
        Self::Holon(Box::new(HolonError::Linear(error)))
    }
}

/// [definition] **A graded causal complex read as the core complex**, with the causal cell of every
/// core coordinate, degree by degree, in ascending identity order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoreCellChart {
    complex: CellComplex,
    cells: Vec<Vec<CausalCellId>>,
}

impl CoreCellChart {
    /// Build the chart from coordinates per degree and the oriented incidence of each coordinate
    /// cell (its faces with their group-completed coefficient). Faces outside the coordinates are
    /// dropped, which is the relative complex when the caller declared one.
    pub(crate) fn from_incidence(
        cells: Vec<Vec<CausalCellId>>,
        faces_of: impl Fn(CausalCellId) -> Vec<(CausalCellId, Rat)>,
    ) -> Result<Self, CoreChartRefusal> {
        let cells = if cells.is_empty() {
            vec![Vec::new()]
        } else {
            cells
        };
        let mut boundaries = Vec::with_capacity(cells.len() - 1);
        for degree in 1..cells.len() {
            let row_of: BTreeMap<CausalCellId, usize> = cells[degree - 1]
                .iter()
                .enumerate()
                .map(|(at, cell)| (*cell, at))
                .collect();
            let mut rows = vec![vec![Rat::zero(); cells[degree].len()]; cells[degree - 1].len()];
            for (column, cell) in cells[degree].iter().enumerate() {
                for (face, coefficient) in faces_of(*cell) {
                    if let Some(row) = row_of.get(&face) {
                        rows[*row][column] += coefficient;
                    }
                }
            }
            boundaries.push(ExactRatMatrix::shaped(
                cells[degree - 1].len(),
                cells[degree].len(),
                rows,
            )?);
        }
        let complex = CellComplex::new(cells.iter().map(Vec::len).collect(), boundaries)?;
        Ok(Self { complex, cells })
    }

    /// The core complex.
    pub fn complex(&self) -> &CellComplex {
        &self.complex
    }

    pub fn into_complex(self) -> CellComplex {
        self.complex
    }

    /// The causal cells of one degree, in the core coordinate order.
    pub fn cells(&self, degree: usize) -> &[CausalCellId] {
        self.cells.get(degree).map(Vec::as_slice).unwrap_or(&[])
    }

    /// The degree and coordinate of one causal cell.
    pub fn position(&self, cell: CausalCellId) -> Option<(usize, usize)> {
        self.cells.iter().enumerate().find_map(|(degree, cells)| {
            cells
                .iter()
                .position(|candidate| *candidate == cell)
                .map(|at| (degree, at))
        })
    }

    /// A causal chain of one degree as a core chain vector (the group completion of each
    /// coefficient). A cell of another degree, or outside the chart, is refused.
    pub fn chain(&self, degree: usize, chain: &CausalChain) -> Result<Vec<Rat>, CoreChartRefusal> {
        let mut vector = vec![Rat::zero(); self.cells(degree).len()];
        for (cell, coefficient) in chain.coefficients() {
            match self.position(*cell) {
                Some((found, at)) if found == degree => {
                    vector[at] += Rat::from_integer(coefficient.difference());
                }
                _ => {
                    return Err(CausalAlgebraicError::Law(
                        crate::CausalAlgebraicRefusal::MissingCausalCell(*cell),
                    )
                    .into());
                }
            }
        }
        Ok(vector)
    }
}

impl GradedCausalComplex {
    /// [definition] **This complex as the core complex `K`** (see the module header): every cell,
    /// by grade, with `∂_k` the group-completed boundary coefficients. `∂∘∂ = 0` is re-certified by
    /// the core constructor.
    pub fn core_chart(&self) -> Result<CoreCellChart, CoreChartRefusal> {
        let top = self.dimension().map_or(0, |grade| grade as usize);
        let mut cells = vec![Vec::new(); top + 1];
        for (id, cell) in self.cells() {
            cells[cell.grade as usize].push(*id);
        }
        CoreCellChart::from_incidence(cells, |id| {
            self.cells()
                .get(&id)
                .map(|cell| {
                    cell.boundary
                        .coefficients()
                        .iter()
                        .map(|(face, coefficient)| {
                            (*face, Rat::from_integer(coefficient.difference()))
                        })
                        .collect()
                })
                .unwrap_or_default()
        })
    }

    /// [definition] **A core complex founded as a graded causal complex**, every cell caused by
    /// `source_event` and named `{name}[degree:index]`. The boundary must be integral: an integer
    /// coefficient is read as that many passages of one hand. The returned chart is the new
    /// complex's own, whose core complex equals the input.
    pub fn from_core(
        complex: &CellComplex,
        name: &str,
        source_event: EventId,
    ) -> Result<(Self, CoreCellChart), CoreChartRefusal> {
        let mut graded = Self::default();
        let mut founded: Vec<Vec<CausalCellId>> = Vec::with_capacity(complex.dimension() + 1);
        let events = BTreeSet::from([source_event]);
        for degree in 0..=complex.dimension() {
            let mut ids = Vec::with_capacity(complex.cells(degree));
            for index in 0..complex.cells(degree) {
                let mut boundary = CausalChain::default();
                if let Some(matrix) = complex.boundary(degree) {
                    for (row, face) in founded[degree - 1].iter().enumerate() {
                        let value = matrix.get(row, index)?;
                        if value.is_zero() {
                            continue;
                        }
                        if !value.denom().is_one() {
                            return Err(CoreChartRefusal::NonIntegralIncidence {
                                degree,
                                row,
                                column: index,
                            });
                        }
                        boundary.add_term(
                            *face,
                            ComparativeMultiplicity::from_bigint(value.numer().clone()),
                        );
                    }
                }
                ids.push(graded.found_cell(
                    format!("{name}[{degree}:{index}]"),
                    events.clone(),
                    u32::try_from(degree).map_err(|_| {
                        CausalAlgebraicError::Law(crate::CausalAlgebraicRefusal::ArithmeticOverflow)
                    })?,
                    boundary,
                )?);
            }
            founded.push(ids);
        }
        let chart = graded.core_chart()?;
        Ok((graded, chart))
    }
}

impl TryFrom<&GradedCausalComplex> for CellComplex {
    type Error = CoreChartRefusal;

    fn try_from(complex: &GradedCausalComplex) -> Result<Self, Self::Error> {
        Ok(complex.core_chart()?.into_complex())
    }
}

/// [definition] **A graph-shaped engine complex read as the core one-dimensional complex**, with its
/// vertex and edge identities in the core coordinate order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GraphChart<V, E> {
    complex: CellComplex,
    vertices: Vec<V>,
    edges: Vec<E>,
    source: Vec<usize>,
    target: Vec<usize>,
}

impl<V: Ord + Copy, E: Ord + Copy> GraphChart<V, E> {
    /// Build the chart over declared vertices and oriented edges `(edge, source, target)`, in the
    /// given orders. An endpoint outside the vertices or a repeated identity is refused.
    pub fn new(
        vertices: impl IntoIterator<Item = V>,
        edges: impl IntoIterator<Item = (E, V, V)>,
    ) -> Result<Self, CoreChartRefusal> {
        let vertices: Vec<V> = vertices.into_iter().collect();
        let index: BTreeMap<V, usize> = vertices
            .iter()
            .enumerate()
            .map(|(at, vertex)| (*vertex, at))
            .collect();
        if index.len() != vertices.len() {
            return Err(CoreChartRefusal::RepeatedIdentity { what: "vertices" });
        }
        let mut ids = Vec::new();
        let mut source = Vec::new();
        let mut target = Vec::new();
        for (at, (edge, tail, head)) in edges.into_iter().enumerate() {
            let (Some(tail), Some(head)) = (index.get(&tail), index.get(&head)) else {
                return Err(CoreChartRefusal::EndpointOutside { edge: at });
            };
            ids.push(edge);
            source.push(*tail);
            target.push(*head);
        }
        if ids.iter().collect::<BTreeSet<_>>().len() != ids.len() {
            return Err(CoreChartRefusal::RepeatedIdentity { what: "edges" });
        }
        let complex = CellComplex::graph(vertices.len(), &source, &target)?;
        Ok(Self {
            complex,
            vertices,
            edges: ids,
            source,
            target,
        })
    }

    pub fn complex(&self) -> &CellComplex {
        &self.complex
    }

    pub fn vertices(&self) -> &[V] {
        &self.vertices
    }

    pub fn edges(&self) -> &[E] {
        &self.edges
    }

    pub fn vertex_position(&self, vertex: V) -> Option<usize> {
        self.vertices.binary_search(&vertex).ok().or_else(|| {
            self.vertices
                .iter()
                .position(|candidate| *candidate == vertex)
        })
    }

    pub fn edge_position(&self, edge: E) -> Option<usize> {
        self.edges.iter().position(|candidate| *candidate == edge)
    }

    /// The core connection on this graph with one scalar transport per edge
    /// (`Holon/Complex.lean::connectionIncidence`).
    pub fn connection(
        &self,
        transports: Vec<Rat>,
    ) -> Result<ConnectionIncidence, CoreChartRefusal> {
        Ok(ConnectionIncidence::new(
            self.vertices.len(),
            self.source.clone(),
            self.target.clone(),
            transports,
        )?)
    }

    /// The trivial connection; its matrix is the complex's `d₀`.
    pub fn flat_connection(&self) -> Result<ConnectionIncidence, CoreChartRefusal> {
        self.connection(vec![Rat::one(); self.edges.len()])
    }
}

#[cfg(test)]
mod tests;
