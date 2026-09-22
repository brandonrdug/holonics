//! **The complex `K` and its connection-valued incidence `d_A`.**
//!
//! [definition] Oriented cells with boundary `∂`, `∂∘∂ = 0` validated at construction
//! ([`CellComplex`]). A connection twists the incidence: `(d_A φ)_e = g_e φ(t e) − φ(s e)`
//! (`Holon/Complex.lean::connectionIncidence`, `Holon/Complex.lean::connectionIncidence_mulVec`).
//! The covariant difference telescopes along a walk (`Holon/Complex.lean::walkRead_connection`),
//! so on every cell given as a closed walk the exact effort reads `(hol − 1) φ(base)`
//! (`Holon/Complex.lean::cell_curvature`; the triangle form is `Holon/Complex.lean::dA_squared`):
//! the curvature face. The Kirchhoff structure of `d_A` is Dirac for every connection
//! (`Holon/Complex.lean::connectionIncidence_isDirac`), and a flat connection is exactly closed
//! (`Holon/Complex.lean::exact_closed_iff_flat`).
//!
//! [definition; agent-inferred] The complex is constructed from boundary matrices here; the engine
//! adapter from `GradedCausalComplex`/`HodgeOperator` arrives with plan phase 4.
//!
//! | Lean | Rust |
//! |---|---|
//! | `connectionIncidence`, `connectionIncidence_mulVec` | [`ConnectionIncidence::matrix`] |
//! | `IsWalk` | [`ConnectionIncidence::is_walk`] |
//! | `walkRead`, `walkTransport`, `walkRead_connection` | [`ConnectionIncidence::walk_read`], [`ConnectionIncidence::walk_transport`] |
//! | `cell_curvature`, `dA_squared` | [`ConnectionIncidence::curvature`], [`ConnectionIncidence::cell_reading`] |
//! | `connectionIncidence_isDirac`, `connection_isDirac` | [`ConnectionIncidence::kirchhoff`] |
//! | `curved_witness`, `seam_curvature_witness` | tests |

use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::Serialize;

use crate::dirac::DiracStructure;
use crate::exact_linear::ExactRatMatrix;
use crate::holon::HolonError;
use crate::scalar::{at, is_zero, matrix};

/// [definition] **An oriented cell complex**: cell counts per degree and boundary matrices
/// `∂_(k+1) : C_(k+1) → C_k` (`cells[k] × cells[k+1]`), with `∂_k ∂_(k+1) = 0` checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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
    pub fn coboundary(&self, degree: usize) -> Result<Option<ExactRatMatrix>, HolonError> {
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

    /// The Kirchhoff structure of `d₀` (`Holon/Dirac.lean::kirchhoff`).
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
}

/// [definition] **A graph with edge transports** `g_e ≠ 0`
/// (`Holon/Complex.lean::connectionIncidence`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConnectionIncidence {
    vertices: usize,
    source: Vec<usize>,
    target: Vec<usize>,
    transport: Vec<Rat>,
}

impl ConnectionIncidence {
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
        for edge in 0..edges {
            if source[edge] >= vertices || target[edge] >= vertices {
                return Err(HolonError::NotAGraphEdge { edge });
            }
            if transport[edge].is_zero() {
                return Err(HolonError::ZeroTransport { edge });
            }
        }
        Ok(Self {
            vertices,
            source,
            target,
            transport,
        })
    }

    /// The trivial connection (every transport `1`).
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
        self.vertices
    }

    /// `d_A` as an `edges × vertices` matrix: `(d_A φ)_e = g_e φ(t e) − φ(s e)`.
    pub fn matrix(&self) -> Result<ExactRatMatrix, HolonError> {
        Ok(matrix(self.edges(), self.vertices, |edge, vertex| {
            let mut entry = Rat::zero();
            if vertex == self.target[edge] {
                entry += &self.transport[edge];
            }
            if vertex == self.source[edge] {
                entry -= Rat::one();
            }
            entry
        })?)
    }

    /// `Holon/Complex.lean::IsWalk`: consecutive edges chain from `from` to `to`.
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

    /// `Holon/Complex.lean::walkRead`: `ω_e + g_e · read(rest)`, transported to the start.
    pub fn walk_read(&self, cochain: &[Rat], walk: &[usize]) -> Result<Rat, HolonError> {
        if cochain.len() != self.edges() {
            return Err(HolonError::Shape {
                what: "edge cochain",
                expected: self.edges(),
                found: cochain.len(),
            });
        }
        let mut read = Rat::zero();
        for edge in walk.iter().rev() {
            if *edge >= self.edges() {
                return Err(HolonError::NotAGraphEdge { edge: *edge });
            }
            read = &cochain[*edge] + &self.transport[*edge] * read;
        }
        Ok(read)
    }

    /// `Holon/Complex.lean::walkTransport`: the product of the transports along a walk.
    pub fn walk_transport(&self, walk: &[usize]) -> Result<Rat, HolonError> {
        walk.iter().try_fold(Rat::one(), |product, edge| {
            self.transport
                .get(*edge)
                .map(|g| product * g)
                .ok_or(HolonError::NotAGraphEdge { edge: *edge })
        })
    }

    /// [definition] **The curvature face** of a cell given as a closed walk at `base`:
    /// `hol − 1` (`Holon/Complex.lean::cell_curvature`). Refuses a walk that does not close.
    pub fn curvature(&self, cell: &[usize], base: usize) -> Result<Rat, HolonError> {
        if !self.is_walk(base, base, cell) {
            return Err(HolonError::NotAClosedWalk);
        }
        Ok(self.walk_transport(cell)? - Rat::one())
    }

    /// The two sides of `Holon/Complex.lean::cell_curvature` on a potential `φ`: the covariant
    /// face reading of the exact effort `d_A φ` and `(hol − 1) φ(base)`. They are equal.
    pub fn cell_reading(
        &self,
        potential: &[Rat],
        cell: &[usize],
        base: usize,
    ) -> Result<(Rat, Rat), HolonError> {
        let curvature = self.curvature(cell, base)?;
        let effort = self.matrix()?.apply(potential)?;
        Ok((self.walk_read(&effort, cell)?, curvature * &potential[base]))
    }

    /// The Kirchhoff structure of `d_A`, Dirac for every connection
    /// (`Holon/Complex.lean::connectionIncidence_isDirac`).
    pub fn kirchhoff(&self) -> Result<DiracStructure, HolonError> {
        DiracStructure::kirchhoff(&self.matrix()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{int, integer_matrix, ints};

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

    /// `Holon/Conformance.lean::triangle_face_complex`, and a face that is not a cycle is refused.
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

    /// `Holon/Complex.lean::curved_witness`: holonomy 2, still Dirac, `d_A² δ₀ = 1`.
    #[test]
    fn a_curved_triangle_is_dirac_and_not_closed() {
        let complex = triangle_complex();
        let connection = complex.connection(vec![int(2), int(1), int(1)]).unwrap();
        assert!(connection.kirchhoff().is_ok());
        let (reading, curvature_side) = connection
            .cell_reading(&ints(&[1, 0, 0]), &[0, 1, 2], 0)
            .unwrap();
        assert_eq!(reading, int(1));
        assert_eq!(reading, curvature_side);
        // A flat (pure-gauge) connection closes every exact effort (exact_closed_iff_flat).
        let flat = complex
            .connection(vec![int(2), int(3), crate::scalar::rat(1, 6)])
            .unwrap();
        assert!(flat.curvature(&[0, 1, 2], 0).unwrap().is_zero());
        let (reading, _) = flat
            .cell_reading(&ints(&[5, -7, 2]), &[0, 1, 2], 0)
            .unwrap();
        assert!(reading.is_zero());
    }

    /// `Holon/Complex.lean::seam_curvature_witness`: an orientation-reversing seam reads `−2`.
    #[test]
    fn an_orientation_reversing_seam_reads_minus_two() {
        let seam =
            ConnectionIncidence::new(2, vec![0, 1], vec![1, 0], vec![int(1), int(-1)]).unwrap();
        let (reading, side) = seam.cell_reading(&ints(&[1, 0]), &[0, 1], 0).unwrap();
        assert_eq!(reading, int(-2));
        assert_eq!(reading, side);
        assert_eq!(seam.curvature(&[0], 0), Err(HolonError::NotAClosedWalk));
    }

    /// `Holon/Complex.lean::walkRead_connection`: telescoping along an open walk.
    #[test]
    fn the_covariant_difference_telescopes_along_a_walk() {
        let c = ConnectionIncidence::new(
            3,
            vec![0, 1],
            vec![1, 2],
            vec![int(3), crate::scalar::rat(1, 2)],
        )
        .unwrap();
        let phi = ints(&[4, -1, 6]);
        let effort = c.matrix().unwrap().apply(&phi).unwrap();
        let read = c.walk_read(&effort, &[0, 1]).unwrap();
        assert_eq!(read, c.walk_transport(&[0, 1]).unwrap() * &phi[2] - &phi[0]);
    }
}
