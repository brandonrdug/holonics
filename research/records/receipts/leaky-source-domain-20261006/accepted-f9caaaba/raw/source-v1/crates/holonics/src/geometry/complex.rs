//! **The complex `K` and its connection-valued incidence `d_A`.**
//!
//! [definition] Oriented cells with boundary `∂`, `∂∘∂ = 0` validated at construction
//! ([`CellComplex`]). A connection twists the incidence: `(d_A φ)_e = g_e φ(t e) − φ(s e)`
//! (`Holon/Complex.connectionIncidence`, `Holon/Complex.connectionIncidence_mulVec`). Its transports
//! may be **blocks** (rebuild step 4 addition 2, review F4): vertex `v` carries `ℚ^(n_v)` and edge
//! `e` a nonzero `n_(s e) × n_(t e)` matrix `T_e`, not necessarily invertible, with
//! `(d_A φ)_e = T_e φ(t e) − φ(s e)` (`Holon/Complex.blockIncidence`). The telescoping, the curvature
//! face and the Dirac property hold verbatim with matrix transports (`blockWalkRead_incidence`,
//! `block_cell_curvature`, and `Holon/Dirac.kirchhoff_isDirac` for every incidence); a flat block
//! connection closes every exact effort, so the covariant face coboundary composes with `d_A` to
//! zero (`block_flat_closed`, [`ConnectionIncidence::face_coboundary`]). The HNN's contacts are
//! such blocks: the partial isometry `U_aᵀ = ι_(a,g) ι_(a,h)ᵀ` of contact `a = (g→h)` is its
//! transport from ring `h`'s realified nodes to ring `g`'s (`crate::hnn::Field::connection`).
//! The covariant difference telescopes along a walk (`Holon/Complex.walkRead_connection`),
//! so on every cell given as a closed walk the exact effort reads `(hol − 1) φ(base)`
//! (`Holon/Complex.cell_curvature`; the triangle form is `Holon/Complex.dA_squared`):
//! the curvature face. The Kirchhoff structure of `d_A` is Dirac for every connection
//! (`Holon/Complex.connectionIncidence_isDirac`), and a flat connection is exactly closed
//! (`Holon/Complex.exact_closed_iff_flat`).
//!
//! [definition; agent-inferred] The complex is constructed from boundary matrices here, or from an
//! oriented graph ([`CellComplex::graph`]); it carries only the incidence.
//!
//! [definition] **A declared metric is storage.** A Hodge metric `W_k` on each degree is a positive
//! definite storage form (`crate::holon::element::ElementRelation::Storage`); the codifferential is its
//! metric adjoint `δ_k = W_k⁻¹ d_kᵀ W_(k+1)` ([`CellComplex::codifferential`]) and the Hodge
//! operator `Δ_k = d_(k−1) δ_(k−1) + δ_k d_k` ([`CellComplex::hodge_laplacian`]). A metric with a
//! negative or zero direction is refused by its inertia.
//!
//! | Lean | Rust |
//! |---|---|
//! | `connectionIncidence`, `connectionIncidence_mulVec`; `blockIncidence`, `blockIncidence_eq_connectionIncidence` | [`ConnectionIncidence::matrix`], [`ConnectionIncidence::blocks`] |
//! | `IsWalk` | [`ConnectionIncidence::is_walk`] |
//! | `walkRead`, `walkTransport`, `walkRead_connection`; `blockWalkRead`, `blockWalkTransport`, `blockWalkRead_incidence` | [`ConnectionIncidence::walk_read`], [`ConnectionIncidence::walk_transport`] |
//! | `cell_curvature`, `dA_squared`, `block_cell_curvature` | [`ConnectionIncidence::curvature`], [`ConnectionIncidence::cell_reading`] |
//! | `block_flat_closed` | [`ConnectionIncidence::face_coboundary`] |
//! | `connectionIncidence_isDirac`, `connection_isDirac`; `Holon/Dirac.kirchhoff_isDirac` (every block matrix) | [`ConnectionIncidence::kirchhoff`] |
//! | `curved_witness`, `seam_curvature_witness` | tests |

use crate::ratio::Rat;
use num_traits::{One, Zero};

use crate::holon::HolonError;
use crate::holon::dirac::DiracStructure;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::{SymmetricForm, inertia};
use crate::ratio::linear::vector::{add, at, form_matrix, is_zero, matrix};

/// [definition] **An oriented cell complex**: cell counts per degree and boundary matrices
/// `∂_(k+1) : C_(k+1) → C_k` (`cells[k] × cells[k+1]`), with `∂_k ∂_(k+1) = 0` checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellComplex {
    cells: Vec<usize>,
    boundaries: Vec<ExactRatMatrix>,
}

impl CellComplex {
    /// Validate shapes and `∂∘∂ = 0`; a failing composite is refused by the degree it fails at.
    pub fn new(cells: Vec<usize>, boundaries: Vec<ExactRatMatrix>) -> Result<Self, HolonError> {
        if cells.is_empty() || boundaries.len() + 1 != cells.len() {
            return Err(HolonError::Shape {
                what: "boundary maps (one fewer than cell degrees)",
                expected: cells.len().saturating_sub(1),
                found: boundaries.len(),
            });
        }
        for (k, boundary) in boundaries.iter().enumerate() {
            if boundary.rows() != cells[k] || boundary.columns() != cells[k + 1] {
                return Err(HolonError::Shape {
                    what: "boundary map shape",
                    expected: cells[k] * cells[k + 1],
                    found: boundary.rows() * boundary.columns(),
                });
            }
        }
        for k in 1..boundaries.len() {
            let composite = boundaries[k - 1].multiply(&boundaries[k])?;
            if !is_zero(composite.entries()) {
                return Err(HolonError::BoundaryNotClosed { degree: k + 1 });
            }
        }
        Ok(Self { cells, boundaries })
    }

    /// The top degree.
    pub fn dimension(&self) -> usize {
        self.cells.len() - 1
    }

    pub fn cells(&self, degree: usize) -> usize {
        self.cells.get(degree).copied().unwrap_or(0)
    }

    /// `∂_k : C_k → C_(k−1)`, for `1 ≤ k ≤ dimension`.
    pub fn boundary(&self, degree: usize) -> Option<&ExactRatMatrix> {
        degree
            .checked_sub(1)
            .and_then(|index| self.boundaries.get(index))
    }

    /// `d_k = ∂_(k+1)ᵀ : C^k → C^(k+1)`.
    pub(crate) fn coboundary(&self, degree: usize) -> Result<Option<ExactRatMatrix>, HolonError> {
        Ok(match self.boundary(degree + 1) {
            Some(boundary) => Some(boundary.transpose()?),
            None => None,
        })
    }

    /// The edge–node incidence `d₀ = ∂₁ᵀ` (`edges × nodes`), the Kirchhoff incidence.
    pub fn incidence(&self) -> Result<ExactRatMatrix, HolonError> {
        match self.coboundary(0)? {
            Some(d) => Ok(d),
            None => Err(HolonError::Shape {
                what: "complex dimension for an edge incidence",
                expected: 1,
                found: 0,
            }),
        }
    }

    /// The Kirchhoff structure of `d₀` (`Holon/Dirac.kirchhoff`).
    pub fn kirchhoff(&self) -> Result<DiracStructure, HolonError> {
        DiracStructure::kirchhoff(&self.incidence()?)
    }

    /// The connection on this complex's 1-skeleton: each edge column of `∂₁` must carry exactly
    /// one `−1` (its source) and one `+1` (its target).
    pub fn connection(&self, transports: Vec<Rat>) -> Result<ConnectionIncidence, HolonError> {
        let boundary = self.boundary(1).ok_or(HolonError::Shape {
            what: "complex dimension for a connection",
            expected: 1,
            found: 0,
        })?;
        let (vertices, edges) = (boundary.rows(), boundary.columns());
        let mut source = Vec::with_capacity(edges);
        let mut target = Vec::with_capacity(edges);
        for edge in 0..edges {
            let mut s = None;
            let mut t = None;
            for vertex in 0..vertices {
                let entry = at(boundary, vertex, edge);
                if entry == -Rat::one() && s.is_none() {
                    s = Some(vertex);
                } else if entry == Rat::one() && t.is_none() {
                    t = Some(vertex);
                } else if !entry.is_zero() {
                    return Err(HolonError::NotAGraphEdge { edge });
                }
            }
            match (s, t) {
                (Some(s), Some(t)) => {
                    source.push(s);
                    target.push(t);
                }
                _ => return Err(HolonError::NotAGraphEdge { edge }),
            }
        }
        ConnectionIncidence::new(vertices, source, target, transports)
    }

    /// [definition] **An oriented graph as a one-dimensional complex**: `∂₁` has `−1` at each edge's
    /// source and `+1` at its target, so `d₀ = ∂₁ᵀ` reads `(d₀ φ)_e = φ(t e) − φ(s e)`. A self-loop
    /// is a lawful cell whose boundary column is zero (its two attachments cancel).
    pub fn graph(vertices: usize, source: &[usize], target: &[usize]) -> Result<Self, HolonError> {
        if target.len() != source.len() {
            return Err(HolonError::Shape {
                what: "edge targets",
                expected: source.len(),
                found: target.len(),
            });
        }
        let edges = source.len();
        for edge in 0..edges {
            if source[edge] >= vertices || target[edge] >= vertices {
                return Err(HolonError::NotAGraphEdge { edge });
            }
        }
        let boundary = matrix(vertices, edges, |vertex, edge| {
            let mut entry = Rat::zero();
            if vertex == target[edge] {
                entry += Rat::one();
            }
            if vertex == source[edge] {
                entry -= Rat::one();
            }
            entry
        })?;
        Self::new(vec![vertices, edges], vec![boundary])
    }

    /// Check a declared metric of one degree: its extent is the cell count and it is positive
    /// definite (a lawful storage form); a negative direction is refused with its inertia, a zero
    /// direction as singular.
    fn check_metric(&self, degree: usize, metric: &SymmetricForm) -> Result<(), HolonError> {
        if metric.extent() != self.cells(degree) {
            return Err(HolonError::Shape {
                what: "metric extent (cells of its degree)",
                expected: self.cells(degree),
                found: metric.extent(),
            });
        }
        if metric.extent() == 0 {
            return Ok(());
        }
        let reading = inertia(metric);
        if reading.negative > 0 {
            return Err(HolonError::NotPassive { inertia: reading });
        }
        if reading.zero > 0 {
            return Err(HolonError::Singular {
                what: "a declared cell metric",
            });
        }
        Ok(())
    }

    /// [definition] **The codifferential** `δ_k = W_k⁻¹ d_kᵀ W_(k+1) : C^(k+1) → C^k`, the metric
    /// adjoint of `d_k` under the storage forms `domain = W_k` and `codomain = W_(k+1)`:
    /// `⟨d_k x, y⟩_(W_(k+1)) = ⟨x, δ_k y⟩_(W_k)`. The zero map of the declared shape when either
    /// degree is empty.
    pub fn codifferential(
        &self,
        degree: usize,
        domain: &SymmetricForm,
        codomain: &SymmetricForm,
    ) -> Result<ExactRatMatrix, HolonError> {
        self.check_metric(degree, domain)?;
        self.check_metric(degree + 1, codomain)?;
        let (lower, upper) = (self.cells(degree), self.cells(degree + 1));
        if lower == 0 || upper == 0 {
            return Ok(ExactRatMatrix::zero(lower, upper)?);
        }
        let coboundary = self.coboundary(degree)?.ok_or(HolonError::Shape {
            what: "complex dimension for a codifferential",
            expected: degree + 1,
            found: self.dimension(),
        })?;
        Ok(coboundary.metric_adjoint(&form_matrix(domain), &form_matrix(codomain))?)
    }

    /// [definition] **The Hodge operator** `Δ_k = d_(k−1) δ_(k−1) + δ_k d_k` under one declared
    /// metric per degree (`metrics[k] = W_k`, one per degree `0..=dimension`).
    pub fn hodge_laplacian(
        &self,
        degree: usize,
        metrics: &[SymmetricForm],
    ) -> Result<ExactRatMatrix, HolonError> {
        if metrics.len() != self.cells.len() {
            return Err(HolonError::Shape {
                what: "metrics (one per degree)",
                expected: self.cells.len(),
                found: metrics.len(),
            });
        }
        if degree > self.dimension() {
            return Err(HolonError::Shape {
                what: "Hodge degree",
                expected: self.dimension(),
                found: degree,
            });
        }
        let extent = self.cells(degree);
        let up = match self.coboundary(degree)? {
            Some(coboundary) => self
                .codifferential(degree, &metrics[degree], &metrics[degree + 1])?
                .multiply(&coboundary)?,
            None => ExactRatMatrix::zero(extent, extent)?,
        };
        let down = match degree.checked_sub(1) {
            Some(lower) => self.coboundary(lower)?.map_or_else(
                || Ok(ExactRatMatrix::zero(extent, extent)?),
                |coboundary| -> Result<ExactRatMatrix, HolonError> {
                    Ok(coboundary.multiply(&self.codifferential(
                        lower,
                        &metrics[lower],
                        &metrics[degree],
                    )?)?)
                },
            )?,
            None => ExactRatMatrix::zero(extent, extent)?,
        };
        Ok(down.add(&up)?)
    }

    /// [proved-standard] **The rational Betti number** `b_k = n_k − rank ∂_k − rank ∂_(k+1)`, the
    /// free rank of `H_k` over `ℚ` (torsion is not seen by a rational reading).
    pub fn betti(&self, degree: usize) -> Result<usize, HolonError> {
        let rank = |matrix: Option<&ExactRatMatrix>| -> Result<usize, HolonError> {
            Ok(match matrix {
                Some(matrix) if matrix.rows() > 0 && matrix.columns() > 0 => matrix.rank()?,
                _ => 0,
            })
        };
        let incoming = rank(self.boundary(degree))?;
        let outgoing = rank(self.boundary(degree + 1))?;
        Ok(self.cells(degree) - incoming - outgoing)
    }
}

/// [definition] **A graph with edge transports**, scalar or block (`Holon/Complex.connectionIncidence`,
/// `blockIncidence`). Each vertex `v` carries a space `ℚ^(n_v)` (`n_v = 1` for a scalar
/// connection) and each edge `e` a transport `T_e : ℚ^(n_(t e)) → ℚ^(n_(s e))`, a nonzero exact
/// matrix: `(d_A φ)_e = T_e φ(t e) − φ(s e) ∈ ℚ^(n_(s e))`. A scalar connection is the block one
/// with `1 × 1` transports `g_e ≠ 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConnectionIncidence {
    dimensions: Vec<usize>,
    source: Vec<usize>,
    target: Vec<usize>,
    transport: Vec<ExactRatMatrix>,
}

impl ConnectionIncidence {
    /// A scalar connection: one transport `g_e ≠ 0` per edge.
    pub fn new(
        vertices: usize,
        source: Vec<usize>,
        target: Vec<usize>,
        transport: Vec<Rat>,
    ) -> Result<Self, HolonError> {
        let edges = source.len();
        if target.len() != edges || transport.len() != edges {
            return Err(HolonError::Shape {
                what: "edge targets and transports",
                expected: edges,
                found: target.len().min(transport.len()),
            });
        }
        let blocks = transport
            .into_iter()
            .map(|g| Ok(ExactRatMatrix::from_diagonal(vec![g])?))
            .collect::<Result<Vec<_>, HolonError>>()?;
        Self::blocks(vec![1; vertices], source, target, blocks)
    }

    /// [definition] **A block connection** (rebuild step 4 addition 2, review F4): vertex `v` carries
    /// `ℚ^(dimensions[v])` and edge `e` the transport `T_e`, a `n_(s e) × n_(t e)` exact matrix that
    /// is not zero (a partial isometry is admitted: it need not be invertible). Refuses a shape
    /// that does not fit its ends and a zero transport.
    pub fn blocks(
        dimensions: Vec<usize>,
        source: Vec<usize>,
        target: Vec<usize>,
        transport: Vec<ExactRatMatrix>,
    ) -> Result<Self, HolonError> {
        let edges = source.len();
        if target.len() != edges || transport.len() != edges {
            return Err(HolonError::Shape {
                what: "edge targets and transports",
                expected: edges,
                found: target.len().min(transport.len()),
            });
        }
        let vertices = dimensions.len();
        for edge in 0..edges {
            if source[edge] >= vertices || target[edge] >= vertices {
                return Err(HolonError::NotAGraphEdge { edge });
            }
            let block = &transport[edge];
            if block.rows() != dimensions[source[edge]]
                || block.columns() != dimensions[target[edge]]
            {
                return Err(HolonError::Shape {
                    what: "edge transport (source dimension × target dimension)",
                    expected: dimensions[source[edge]] * dimensions[target[edge]],
                    found: block.rows() * block.columns(),
                });
            }
            if is_zero(block.entries()) {
                return Err(HolonError::ZeroTransport { edge });
            }
        }
        Ok(Self {
            dimensions,
            source,
            target,
            transport,
        })
    }

    /// The trivial scalar connection (every transport `1`).
    pub fn flat(
        vertices: usize,
        source: Vec<usize>,
        target: Vec<usize>,
    ) -> Result<Self, HolonError> {
        let transport = vec![Rat::one(); source.len()];
        Self::new(vertices, source, target, transport)
    }

    pub fn edges(&self) -> usize {
        self.source.len()
    }

    pub fn vertices(&self) -> usize {
        self.dimensions.len()
    }

    /// Each edge's source vertex.
    pub fn sources(&self) -> &[usize] {
        &self.source
    }

    /// Each edge's target vertex.
    pub fn targets(&self) -> &[usize] {
        &self.target
    }

    /// Edge `e`'s transport `T_e : ℚ^(n_(t e)) → ℚ^(n_(s e))`.
    pub fn transport(&self, edge: usize) -> Option<&ExactRatMatrix> {
        self.transport.get(edge)
    }

    /// The offset of each vertex's block in `⊕_v ℚ^(n_v)`, and of each edge's in `⊕_e ℚ^(n_(s e))`.
    fn offsets(&self) -> (Vec<usize>, Vec<usize>) {
        let running = |sizes: &mut dyn Iterator<Item = usize>| -> Vec<usize> {
            let mut total = 0;
            sizes
                .map(|size| {
                    let at = total;
                    total += size;
                    at
                })
                .collect()
        };
        let vertex = running(&mut self.dimensions.iter().copied());
        let edge = running(&mut self.source.iter().map(|s| self.dimensions[*s]));
        (vertex, edge)
    }

    /// The extent of the edge cochains `⊕_e ℚ^(n_(s e))`.
    pub fn edge_extent(&self) -> usize {
        self.source.iter().map(|s| self.dimensions[*s]).sum()
    }

    /// The extent of the vertex cochains `⊕_v ℚ^(n_v)`.
    pub fn vertex_extent(&self) -> usize {
        self.dimensions.iter().sum()
    }

    /// The underlying one-dimensional complex ([`CellComplex::graph`]); at the trivial scalar
    /// connection its incidence is [`Self::matrix`].
    pub fn cell_complex(&self) -> Result<CellComplex, HolonError> {
        CellComplex::graph(self.vertices(), &self.source, &self.target)
    }

    /// `d_A` as a block matrix `(Σ_e n_(s e)) × (Σ_v n_v)`: row block `e` holds `T_e` at the
    /// target's columns and `−I` at the source's, `(d_A φ)_e = T_e φ(t e) − φ(s e)`. At scalar
    /// dimensions it is the `edges × vertices` matrix of `connectionIncidence`.
    pub fn matrix(&self) -> Result<ExactRatMatrix, HolonError> {
        let (vertex, edge) = self.offsets();
        let mut rows = vec![vec![Rat::zero(); self.vertex_extent()]; self.edge_extent()];
        for e in 0..self.edges() {
            let (s, t) = (self.source[e], self.target[e]);
            let block = &self.transport[e];
            for i in 0..self.dimensions[s] {
                let row = &mut rows[edge[e] + i];
                for j in 0..self.dimensions[t] {
                    row[vertex[t] + j] += at(block, i, j);
                }
                row[vertex[s] + i] -= Rat::one();
            }
        }
        Ok(ExactRatMatrix::shaped(
            self.edge_extent(),
            self.vertex_extent(),
            rows,
        )?)
    }

    /// `Holon/Complex.IsWalk`: consecutive edges chain from `from` to `to`.
    pub fn is_walk(&self, from: usize, to: usize, walk: &[usize]) -> bool {
        let mut at_vertex = from;
        for edge in walk {
            if *edge >= self.edges() || self.source[*edge] != at_vertex {
                return false;
            }
            at_vertex = self.target[*edge];
        }
        at_vertex == to
    }

    /// `Holon/Complex.walkRead` (`blockWalkRead`): `ω_e + T_e · read(rest)`, transported to the
    /// start, a vector of the walk's first source. Refuses a sequence that is not a walk.
    pub fn walk_read(&self, cochain: &[Rat], walk: &[usize]) -> Result<Vec<Rat>, HolonError> {
        if cochain.len() != self.edge_extent() {
            return Err(HolonError::Shape {
                what: "edge cochain",
                expected: self.edge_extent(),
                found: cochain.len(),
            });
        }
        let Some(first) = walk.first() else {
            return Ok(Vec::new());
        };
        let start = *self
            .source
            .get(*first)
            .ok_or(HolonError::NotAGraphEdge { edge: *first })?;
        let end = walk.iter().try_fold(start, |at_vertex, edge| {
            match (self.source.get(*edge), self.target.get(*edge)) {
                (Some(s), Some(t)) if *s == at_vertex => Ok(*t),
                _ => Err(HolonError::NotAGraphEdge { edge: *edge }),
            }
        })?;
        let (_, edge) = self.offsets();
        let mut read = vec![Rat::zero(); self.dimensions[end]];
        for e in walk.iter().rev() {
            let own = &cochain[edge[*e]..edge[*e] + self.dimensions[self.source[*e]]];
            read = add(own, &self.transport[*e].apply(&read)?);
        }
        Ok(read)
    }

    /// `Holon/Complex.walkTransport` (`blockWalkTransport`): the product `T_(e₁) ⋯ T_(e_k)` along a
    /// walk, from its end's space to its start's. Refuses a sequence that is not a walk.
    pub fn walk_transport(&self, walk: &[usize]) -> Result<ExactRatMatrix, HolonError> {
        let Some(first) = walk.first() else {
            return Err(HolonError::NotAClosedWalk);
        };
        let start = *self
            .source
            .get(*first)
            .ok_or(HolonError::NotAGraphEdge { edge: *first })?;
        let mut product = ExactRatMatrix::identity(self.dimensions[start])?;
        let mut at_vertex = start;
        for edge in walk {
            match (self.source.get(*edge), self.target.get(*edge)) {
                (Some(s), Some(t)) if *s == at_vertex => {
                    product = product.multiply(&self.transport[*edge])?;
                    at_vertex = *t;
                }
                _ => return Err(HolonError::NotAGraphEdge { edge: *edge }),
            }
        }
        Ok(product)
    }

    /// [definition] **The curvature face** of a cell given as a closed walk at `base`:
    /// `hol − I` (`Holon/Complex.cell_curvature`, `block_cell_curvature`). Refuses a walk that does
    /// not close.
    pub fn curvature(&self, cell: &[usize], base: usize) -> Result<ExactRatMatrix, HolonError> {
        if !self.is_walk(base, base, cell) || cell.is_empty() {
            return Err(HolonError::NotAClosedWalk);
        }
        Ok(self
            .walk_transport(cell)?
            .subtract(&ExactRatMatrix::identity(self.dimensions[base])?)?)
    }

    /// The two sides of `Holon/Complex.cell_curvature` on a potential `φ`: the covariant
    /// face reading of the exact effort `d_A φ` and `(hol − I) φ(base)`. They are equal.
    pub fn cell_reading(
        &self,
        potential: &[Rat],
        cell: &[usize],
        base: usize,
    ) -> Result<(Vec<Rat>, Vec<Rat>), HolonError> {
        let curvature = self.curvature(cell, base)?;
        let effort = self.matrix()?.apply(potential)?;
        let (vertex, _) = self.offsets();
        let at_base = &potential[vertex[base]..vertex[base] + self.dimensions[base]];
        Ok((self.walk_read(&effort, cell)?, curvature.apply(at_base)?))
    }

    /// [definition] **The covariant face coboundary** `d_A¹` of cells given as closed walks
    /// `(walk, base)`: row block `c` is the walk reading `ω ↦ walkRead(ω, walk_c) ∈ ℚ^(n_base)`, so
    /// `d_A¹ d_A⁰ φ` is the block of curvatures `(hol_c − I) φ(base_c)`
    /// (`Holon/Complex.block_cell_curvature`). A flat connection (`hol_c = I` on every cell) has
    /// `d_A¹ d_A⁰ = 0`: `∂² = 0` holds covariantly (`block_flat_closed`).
    pub fn face_coboundary(
        &self,
        cells: &[(Vec<usize>, usize)],
    ) -> Result<ExactRatMatrix, HolonError> {
        let extent = self.edge_extent();
        let mut rows: Vec<Vec<Rat>> = Vec::new();
        for (walk, base) in cells {
            if !self.is_walk(*base, *base, walk) || walk.is_empty() {
                return Err(HolonError::NotAClosedWalk);
            }
            let mut columns = Vec::with_capacity(extent);
            for coordinate in 0..extent {
                let mut unit = vec![Rat::zero(); extent];
                unit[coordinate] = Rat::one();
                columns.push(self.walk_read(&unit, walk)?);
            }
            for i in 0..self.dimensions[*base] {
                rows.push(columns.iter().map(|column| column[i].clone()).collect());
            }
        }
        Ok(ExactRatMatrix::shaped(rows.len(), extent, rows)?)
    }

    /// The Kirchhoff structure of `d_A`, Dirac for every connection
    /// (`Holon/Complex.connectionIncidence_isDirac`; for blocks `Holon/Dirac.kirchhoff_isDirac`).
    pub fn kirchhoff(&self) -> Result<DiracStructure, HolonError> {
        DiracStructure::kirchhoff(&self.matrix()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::{integer_matrix, ints};

    fn triangle_complex() -> CellComplex {
        // ∂₁ = d₀ᵀ for the oriented triangle 0→1, 1→2, 2→0; ∂₂ = the one face (1,1,1)ᵀ.
        let d0 = integer_matrix(&[&[-1, 1, 0], &[0, -1, 1], &[1, 0, -1]]).unwrap();
        CellComplex::new(
            vec![3, 3, 1],
            vec![
                d0.transpose().unwrap(),
                integer_matrix(&[&[1], &[1], &[1]]).unwrap(),
            ],
        )
        .unwrap()
    }

    /// `Holon/Conformance.triangle_face_complex`, and a face that is not a cycle is refused.
    #[test]
    fn the_triangle_with_its_face_is_a_complex_and_a_bad_face_is_refused() {
        let complex = triangle_complex();
        assert_eq!(complex.dimension(), 2);
        let d0 = complex.incidence().unwrap();
        let bad = CellComplex::new(
            vec![3, 3, 1],
            vec![
                d0.transpose().unwrap(),
                integer_matrix(&[&[1], &[1], &[0]]).unwrap(),
            ],
        );
        assert_eq!(bad, Err(HolonError::BoundaryNotClosed { degree: 2 }));
    }

    /// `Holon/Complex.curved_witness`: holonomy 2, still Dirac, `d_A² δ₀ = 1`.
    #[test]
    fn a_curved_triangle_is_dirac_and_not_closed() {
        let complex = triangle_complex();
        let connection = complex
            .connection(vec![integer(2), integer(1), integer(1)])
            .unwrap();
        assert!(connection.kirchhoff().is_ok());
        let (reading, curvature_side) = connection
            .cell_reading(&ints(&[1, 0, 0]), &[0, 1, 2], 0)
            .unwrap();
        assert_eq!(reading, ints(&[1]));
        assert_eq!(reading, curvature_side);
        // A flat (pure-gauge) connection closes every exact effort (exact_closed_iff_flat).
        let flat = complex
            .connection(vec![integer(2), integer(3), crate::ratio::rat(1, 6)])
            .unwrap();
        assert!(is_zero(flat.curvature(&[0, 1, 2], 0).unwrap().entries()));
        let (reading, _) = flat
            .cell_reading(&ints(&[5, -7, 2]), &[0, 1, 2], 0)
            .unwrap();
        assert!(is_zero(&reading));
    }

    /// `Holon/Complex.seam_curvature_witness`: an orientation-reversing seam reads `−2`.
    #[test]
    fn an_orientation_reversing_seam_reads_minus_two() {
        let seam =
            ConnectionIncidence::new(2, vec![0, 1], vec![1, 0], vec![integer(1), integer(-1)])
                .unwrap();
        let (reading, side) = seam.cell_reading(&ints(&[1, 0]), &[0, 1], 0).unwrap();
        assert_eq!(reading, ints(&[-2]));
        assert_eq!(reading, side);
        assert_eq!(seam.curvature(&[0], 0), Err(HolonError::NotAClosedWalk));
    }

    /// A graph complex is the flat connection's incidence, and its Betti numbers are the
    /// components and the independent loops.
    #[test]
    fn a_graph_is_a_one_complex_whose_incidence_is_the_flat_connection() {
        let graph = CellComplex::graph(3, &[0, 1, 2], &[1, 2, 0]).unwrap();
        let flat = ConnectionIncidence::flat(3, vec![0, 1, 2], vec![1, 2, 0]).unwrap();
        assert_eq!(graph.incidence().unwrap(), flat.matrix().unwrap());
        assert_eq!(flat.cell_complex().unwrap(), graph);
        assert_eq!((graph.betti(0).unwrap(), graph.betti(1).unwrap()), (1, 1));
        let filled = triangle_complex();
        assert_eq!(
            (0..=2)
                .map(|k| filled.betti(k).unwrap())
                .collect::<Vec<_>>(),
            vec![1, 0, 0]
        );
        assert_eq!(
            CellComplex::graph(2, &[0], &[2]),
            Err(HolonError::NotAGraphEdge { edge: 0 })
        );
    }

    /// The codifferential is the metric adjoint of `d` under positive storage forms, the unit
    /// Hodge operator on the filled triangle is `3·1` at degree 1, and a metric with a negative or
    /// zero direction is refused.
    #[test]
    fn the_codifferential_is_the_storage_adjoint_and_an_indefinite_metric_is_refused() {
        let complex = triangle_complex();
        let w0 = SymmetricForm::from_diagonal(ints(&[1, 2, 3]));
        let w1 = SymmetricForm::from_diagonal(ints(&[5, 1, 2]));
        let delta = complex.codifferential(0, &w0, &w1).unwrap();
        let d0 = complex.coboundary(0).unwrap().unwrap();
        let (x, y) = (ints(&[1, -2, 4]), ints(&[3, 1, -1]));
        let left = crate::ratio::linear::vector::dot(
            &d0.apply(&x).unwrap(),
            &form_matrix(&w1).apply(&y).unwrap(),
        );
        let right = crate::ratio::linear::vector::dot(
            &form_matrix(&w0).apply(&x).unwrap(),
            &delta.apply(&y).unwrap(),
        );
        assert_eq!(left, right);

        let unit = |n: usize| SymmetricForm::from_diagonal(vec![Rat::one(); n]);
        let metrics = vec![unit(3), unit(3), unit(1)];
        let laplacian = complex.hodge_laplacian(1, &metrics).unwrap();
        assert_eq!(
            laplacian,
            ExactRatMatrix::identity(3).unwrap().scaled(&integer(3))
        );

        let indefinite = SymmetricForm::from_diagonal(ints(&[1, -1, 1]));
        assert!(matches!(
            complex.codifferential(0, &indefinite, &w1),
            Err(HolonError::NotPassive { .. })
        ));
        let degenerate = SymmetricForm::from_diagonal(ints(&[1, 0, 1]));
        assert!(matches!(
            complex.codifferential(0, &w0, &degenerate),
            Err(HolonError::Singular { .. })
        ));
    }

    /// `Holon/Complex.walkRead_connection`: telescoping along an open walk.
    #[test]
    fn the_covariant_difference_telescopes_along_a_walk() {
        let c = ConnectionIncidence::new(
            3,
            vec![0, 1],
            vec![1, 2],
            vec![integer(3), crate::ratio::rat(1, 2)],
        )
        .unwrap();
        let phi = ints(&[4, -1, 6]);
        let effort = c.matrix().unwrap().apply(&phi).unwrap();
        let read = c.walk_read(&effort, &[0, 1]).unwrap();
        let transport = c.walk_transport(&[0, 1]).unwrap();
        assert_eq!(read, vec![at(&transport, 0, 0) * &phi[2] - &phi[0]]);
    }

    /// `Holon/Complex.{blockIncidence_eq_connectionIncidence, blockWalkRead_incidence,
    /// block_cell_curvature, block_flat_closed}`, `Holon/Dirac.kirchhoff_isDirac`: with partial-isometry
    /// blocks on vertices of different widths the incidence telescopes along a walk, the face
    /// coboundary of every flat cell composes with `d_A` to zero (`∂² = 0` covariantly), a cell that
    /// drops a coordinate reads its curvature `hol − I`, the Kirchhoff structure is Dirac, and the
    /// underlying complex keeps `∂∘∂ = 0`. A zero or misshapen block is refused.
    #[test]
    fn block_transports_telescope_and_a_flat_cell_closes() {
        // A partial matching `n_s × n_t`: row i of the source takes column i of the target.
        let matching = |rows: usize, columns: usize, width: usize| {
            matrix(rows, columns, |i, j| {
                if i == j && i < width {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            })
            .unwrap()
        };
        // A triangle of vertices of widths 2, 3, 2; edges 0→1, 1→2, 2→0.
        let dimensions = vec![2, 3, 2];
        let flat = ConnectionIncidence::blocks(
            dimensions.clone(),
            vec![0, 1, 2],
            vec![1, 2, 0],
            vec![matching(2, 3, 2), matching(3, 2, 2), matching(2, 2, 2)],
        )
        .unwrap();
        let d = flat.matrix().unwrap();
        assert_eq!((d.rows(), d.columns()), (7, 7));
        let phi = ints(&[1, -2, 3, 5, -1, 4, 2]);
        let effort = d.apply(&phi).unwrap();
        let read = flat.walk_read(&effort, &[0, 1]).unwrap();
        let hol01 = flat.walk_transport(&[0, 1]).unwrap();
        assert_eq!(
            read,
            add(&hol01.apply(&phi[5..7]).unwrap(), &ints(&[-1, 2]))
        );
        let cell = (vec![0, 1, 2], 0);
        assert!(is_zero(flat.curvature(&cell.0, 0).unwrap().entries()));
        let closed = flat
            .face_coboundary(std::slice::from_ref(&cell))
            .unwrap()
            .multiply(&d)
            .unwrap();
        assert!(is_zero(closed.entries()));
        // Narrow the last edge to one coordinate: the cell drops vertex 0's second coordinate.
        let curved = ConnectionIncidence::blocks(
            dimensions,
            vec![0, 1, 2],
            vec![1, 2, 0],
            vec![matching(2, 3, 2), matching(3, 2, 2), matching(2, 2, 1)],
        )
        .unwrap();
        let hol = curved.curvature(&cell.0, 0).unwrap();
        assert_eq!(
            hol,
            matching(2, 2, 2)
                .subtract(&matching(2, 2, 1))
                .unwrap()
                .scaled(&integer(-1))
        );
        let (reading, side) = curved.cell_reading(&phi, &cell.0, 0).unwrap();
        assert_eq!(reading, side);
        assert_eq!(reading, ints(&[0, 2]));
        let face = curved.face_coboundary(&[cell]).unwrap();
        assert_eq!(
            face.multiply(&curved.matrix().unwrap())
                .unwrap()
                .apply(&phi)
                .unwrap(),
            reading
        );
        assert!(curved.kirchhoff().is_ok());
        let complex = curved.cell_complex().unwrap();
        assert_eq!(complex.betti(1).unwrap(), 1);
        // The scalar connection is the block one at unit widths.
        let scalar = ConnectionIncidence::new(2, vec![0], vec![1], vec![integer(3)]).unwrap();
        let unit = ConnectionIncidence::blocks(
            vec![1, 1],
            vec![0],
            vec![1],
            vec![ExactRatMatrix::from_diagonal(vec![integer(3)]).unwrap()],
        )
        .unwrap();
        assert_eq!(scalar, unit);
        assert_eq!(
            ConnectionIncidence::blocks(vec![2, 2], vec![0], vec![1], vec![matching(2, 2, 0)]),
            Err(HolonError::ZeroTransport { edge: 0 })
        );
        assert!(matches!(
            ConnectionIncidence::blocks(vec![2, 3], vec![0], vec![1], vec![matching(2, 2, 2)]),
            Err(HolonError::Shape { .. })
        ));
    }
}
