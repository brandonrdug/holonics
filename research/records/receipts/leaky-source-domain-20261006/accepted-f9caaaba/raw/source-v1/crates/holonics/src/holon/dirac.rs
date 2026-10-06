//! **The interconnection (Dirac) structure `𝒟 = 𝒟^⊥`.**
//!
//! [definition] A Dirac structure is a subspace of the bond space equal to its bond-form
//! orthogonal (`Holon/Dirac.IsDirac`); it is power neutral
//! (`Holon/Dirac.IsDirac.power_eq_zero`). Its presentations are the skew graph
//! (`Holon/Dirac.skewGraph`, `Holon/Dirac.skewGraph_isDirac`), the Kirchhoff incidence
//! (`Holon/Dirac.kirchhoff`, `Holon/Dirac.kirchhoff_isDirac`, Tellegen
//! `Holon/Dirac.tellegen`) and the kernel form `{(f,e) | F f + E e = 0}`
//! (`Holon/Dirac.kernelForm`), Dirac exactly when `F Eᵀ + E Fᵀ = 0` and `rank [F | E] = n`
//! (`Holon/Dirac.kernelForm_isDirac`), whose orthogonal is the image form
//! (`Holon/Dirac.orthogonal_kernelForm`).
//!
//! [definition] **Every structure here is carried in kernel form.** The skew graph is `(1, −J)`
//! (`Holon/Dirac.skewGraph_eq_kernelForm`); the Kirchhoff structure is `([dᵀ;0],[0;Cᵀ])` for a
//! cycle matrix `C` spanning `ker dᵀ` (`Holon/Dirac.kirchhoff_eq_kernelForm`), and
//! [`KernelForm::from_incidence`] builds that `C` as an exact kernel basis
//! (`Holon/Dirac.exists_cycleMatrix`, `Holon/Dirac.kirchhoff_is_kernelForm`). The
//! constraint rows are kept in reduced row echelon form, which is canonical, so two structures are
//! the same subspace exactly when their rows are equal.
//!
//! [definition] **Composition** of a structure on `P × Q` with a link on `Q`
//! (`Holon/Dirac.compose`, `Holon/Dirac.compose_isDirac`), **interconnection** at shared
//! ports with flows opposite and efforts equal (`Holon/Dirac.link`,
//! `Holon/Dirac.interconnect`, `Holon/Dirac.mem_interconnect`,
//! `Holon/Dirac.interconnect_isDirac`, `Holon/Dirac.interconnect_power`), the
//! **pushforward** along a port map (`Holon/Restriction.pushforwardD`,
//! `Holon/Restriction.pushforwardD_isDirac`) and **relabelling**
//! (`Holon/Dirac.bondReindex`, `Holon/Dirac.IsDirac.reindex`) are computed by exact
//! elimination of the internal bond, and every result is re-certified Dirac by the kernel-form test
//! rather than trusted: a failure is a typed refusal naming the obstruction.
//!
//! | Lean | Rust |
//! |---|---|
//! | `IsDirac`, `isDirac_of` | [`KernelForm::is_dirac`], [`DiracStructure`] |
//! | `skewGraph`, `skewGraph_isDirac` | [`DiracStructure::skew_graph`] |
//! | `kirchhoff`, `kirchhoff_isDirac`, `tellegen` | [`DiracStructure::kirchhoff`], [`tellegen`] |
//! | `kernelForm`, `kernelForm_isDirac`, `orthogonal_kernelForm` | [`DiracStructure::kernel_form`], [`KernelForm::orthogonal`] |
//! | `exists_cycleMatrix`, `kirchhoff_is_kernelForm` | [`KernelForm::from_incidence`] |
//! | `compose`, `compose_isDirac` | [`DiracStructure::compose`] |
//! | `interconnect`, `interconnect_isDirac`, `mem_interconnect` | [`DiracStructure::interconnect`] |
//! | `bondReindex`, `IsDirac.reindex` | [`DiracStructure::relabel`] |
//! | `pushforwardD`, `pushforwardD_isDirac`, `mem_pushforwardD` | [`DiracStructure::pushforward`] |
//! | `passiveCoholon`, `passiveCoholon_isDirac` | [`DiracStructure::passive_coholon`] |

use crate::ratio::Rat;
use num_traits::{One, Zero};

use crate::holon::HolonError;
use crate::holon::port::Bond;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{
    at, dot, hstack, is_skew, is_zero, matrix, select_columns, vstack,
};

/// [definition] A subspace of the bond space on `ports` ports, carried by its constraint rows
/// `[F | E]` in reduced row echelon form (independent rows, canonical).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelForm {
    ports: usize,
    constraints: ExactRatMatrix,
}

impl KernelForm {
    /// `{(f, e) | F f + E e = 0}` (`Holon/Dirac.kernelForm`). Any shape-consistent pair is a
    /// subspace; Dirac-ness is a separate test.
    pub fn new(flow: &ExactRatMatrix, effort: &ExactRatMatrix) -> Result<Self, HolonError> {
        if flow.rows() != effort.rows() {
            return Err(HolonError::Shape {
                what: "kernel-form effort rows",
                expected: flow.rows(),
                found: effort.rows(),
            });
        }
        if flow.columns() != effort.columns() {
            return Err(HolonError::Shape {
                what: "kernel-form effort columns",
                expected: flow.columns(),
                found: effort.columns(),
            });
        }
        Self::from_constraints(flow.columns(), &hstack(flow, effort)?)
    }

    /// Canonicalize constraint rows `[F | E]` on `ports` ports.
    fn from_constraints(ports: usize, rows: &ExactRatMatrix) -> Result<Self, HolonError> {
        if rows.columns() != 2 * ports {
            return Err(HolonError::Shape {
                what: "constraint columns",
                expected: 2 * ports,
                found: rows.columns(),
            });
        }
        let (reduced, pivots, _) = rows.reduced_row_echelon()?;
        let rank = pivots.len();
        let constraints = matrix(rank, 2 * ports, |row, column| at(&reduced, row, column))?;
        Ok(Self { ports, constraints })
    }

    /// The span of the listed bonds (`Holon/Dirac.imageMap` when the bonds are the columns
    /// of `[Eᵀ; Fᵀ]`): its constraints are the annihilator of the span.
    pub fn span(ports: usize, bonds: &[Bond]) -> Result<Self, HolonError> {
        for bond in bonds {
            if bond.ports() != ports {
                return Err(HolonError::Shape {
                    what: "spanning bond",
                    expected: ports,
                    found: bond.ports(),
                });
            }
        }
        let vectors: Vec<Vec<Rat>> = bonds.iter().map(Bond::coordinates).collect();
        Self::from_constraints(ports, &annihilator(2 * ports, &vectors)?)
    }

    /// [definition] **The cycle basis and the Kirchhoff kernel form** of an incidence
    /// `d : edges × nodes`: `C` is an exact basis of `ker dᵀ` (`Holon/Dirac.exists_cycleMatrix`)
    /// and the structure is `F = [dᵀ; 0]`, `E = [0; Cᵀ]`
    /// (`Holon/Dirac.kirchhoff_eq_kernelForm`). Returns the form and `C` (`edges × cycles`).
    pub fn from_incidence(
        incidence: &ExactRatMatrix,
    ) -> Result<(Self, ExactRatMatrix), HolonError> {
        let edges = incidence.rows();
        let transposed = incidence.transpose()?;
        let cycles = transposed.kernel_basis()?;
        let cycle_matrix = matrix(edges, cycles.len(), |edge, cycle| {
            cycles[cycle][edge].clone()
        })?;
        let flow = vstack(&transposed, &ExactRatMatrix::zero(cycles.len(), edges)?)?;
        let effort = vstack(
            &ExactRatMatrix::zero(transposed.rows(), edges)?,
            &cycle_matrix.transpose()?,
        )?;
        Ok((Self::new(&flow, &effort)?, cycle_matrix))
    }

    pub fn ports(&self) -> usize {
        self.ports
    }

    /// The canonical constraint rows `[F | E]`.
    pub fn constraints(&self) -> &ExactRatMatrix {
        &self.constraints
    }

    /// `F`, the flow block of the canonical rows.
    pub fn flow_matrix(&self) -> Result<ExactRatMatrix, HolonError> {
        let columns: Vec<usize> = (0..self.ports).collect();
        Ok(select_columns(&self.constraints, &columns)?)
    }

    /// `E`, the effort block of the canonical rows.
    pub fn effort_matrix(&self) -> Result<ExactRatMatrix, HolonError> {
        let columns: Vec<usize> = (self.ports..2 * self.ports).collect();
        Ok(select_columns(&self.constraints, &columns)?)
    }

    /// `rank [F | E]`.
    pub fn rank(&self) -> usize {
        self.constraints.rows()
    }

    /// The dimension `2n − rank [F | E]` of the subspace.
    pub fn dimension(&self) -> usize {
        2 * self.ports - self.rank()
    }

    /// An exact basis of the subspace.
    pub fn basis(&self) -> Result<Vec<Bond>, HolonError> {
        let kernel = if self.rank() == 0 {
            (0..2 * self.ports)
                .map(|axis| {
                    let mut v = crate::ratio::linear::vector::zeros(2 * self.ports);
                    v[axis] = Rat::one();
                    v
                })
                .collect()
        } else {
            self.constraints.kernel_basis()?
        };
        kernel.iter().map(|v| Bond::from_coordinates(v)).collect()
    }

    /// Membership: `F f + E e = 0`.
    pub fn contains(&self, bond: &Bond) -> Result<bool, HolonError> {
        if bond.ports() != self.ports {
            return Err(HolonError::Shape {
                what: "tested bond",
                expected: self.ports,
                found: bond.ports(),
            });
        }
        Ok(is_zero(&self.constraints.apply(&bond.coordinates())?))
    }

    /// [definition] **The bond-form orthogonal** (`Holon/Dirac.orthogonal_kernelForm`): the
    /// constraints of `S^⊥` are the pairing covectors `(e_b, f_b)` of a basis `b` of `S`.
    pub fn orthogonal(&self) -> Result<Self, HolonError> {
        let rows: Vec<Vec<Rat>> = self
            .basis()?
            .iter()
            .map(|bond| {
                let mut row = bond.effort().to_vec();
                row.extend(bond.flow().iter().cloned());
                row
            })
            .collect();
        let rows = matrix(rows.len(), 2 * self.ports, |row, column| {
            rows[row][column].clone()
        })?;
        Self::from_constraints(self.ports, &rows)
    }

    /// Same subspace: equal port counts and equal canonical rows.
    pub fn same_subspace(&self, other: &Self) -> bool {
        self == other
    }

    /// Isotropic: every pair of basis bonds pairs to zero (so every bond has zero power).
    pub fn is_isotropic(&self) -> Result<bool, HolonError> {
        let basis = self.basis()?;
        for (index, left) in basis.iter().enumerate() {
            for right in &basis[index..] {
                if !left.pairing(right)?.is_zero() {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// The kernel-form Dirac test (`Holon/Dirac.kernelForm_isDirac`): `F Eᵀ + E Fᵀ = 0` and
    /// `rank [F | E] = n`. Returns the obstruction as a typed refusal.
    ///
    /// [definition; agent-inferred] The cross form is read port by port: with `A = F Eᵀ`,
    /// `A_(rs) = Σ_k F_rk E_sk` sums only over the ports where row `r` carries a flow and row `s`
    /// an effort, and the test is `A + Aᵀ = 0`. A block-sparse structure (a skew graph, a ring's
    /// port rows) costs its nonzero pairs per port, never a dense product.
    pub fn certify_dirac(&self) -> Result<(), HolonError> {
        if self.rank() != self.ports {
            return Err(HolonError::NotMaximal {
                rank: self.rank(),
                ports: self.ports,
            });
        }
        let n = self.ports;
        let mut flow_at: Vec<Vec<(usize, &Rat)>> = vec![Vec::new(); n];
        let mut effort_at: Vec<Vec<(usize, &Rat)>> = vec![Vec::new(); n];
        for row in 0..self.rank() {
            for (column, value) in self.constraints.row(row)?.iter().enumerate() {
                if value.is_zero() {
                    continue;
                }
                if column < n {
                    flow_at[column].push((row, value));
                } else {
                    effort_at[column - n].push((row, value));
                }
            }
        }
        let mut cross: std::collections::BTreeMap<(usize, usize), Rat> = Default::default();
        for (flows, efforts) in flow_at.iter().zip(&effort_at) {
            for (r, f) in flows {
                for (s, e) in efforts {
                    *cross.entry((*r, *s)).or_default() += *f * *e;
                }
            }
        }
        for ((r, s), value) in &cross {
            let transposed = cross.get(&(*s, *r)).cloned().unwrap_or_default();
            if !(value + transposed).is_zero() {
                return Err(HolonError::NotIsotropic);
            }
        }
        Ok(())
    }

    /// `S = S^⊥`.
    pub fn is_dirac(&self) -> Result<bool, HolonError> {
        Ok(self.certify_dirac().is_ok())
    }
}

/// The covectors annihilating the listed vectors in dimension `extent`, as rows.
fn annihilator(extent: usize, vectors: &[Vec<Rat>]) -> Result<ExactRatMatrix, HolonError> {
    if vectors.is_empty() {
        return Ok(ExactRatMatrix::identity(extent)?);
    }
    let spanned = matrix(vectors.len(), extent, |row, column| {
        vectors[row][column].clone()
    })?;
    let kernel = spanned.kernel_basis()?;
    Ok(matrix(kernel.len(), extent, |row, column| {
        kernel[row][column].clone()
    })?)
}

/// [definition] **Eliminate internal variables.** Given constraint rows on `(x, y)` with `x` the
/// first `keep` coordinates, the rows of `{x | ∃ y, M (x, y) = 0}`: project the exact solution space
/// to `x` and take its annihilator.
fn eliminate(rows: &ExactRatMatrix, keep: usize) -> Result<ExactRatMatrix, HolonError> {
    let total = rows.columns();
    let solutions: Vec<Vec<Rat>> = if rows.rows() == 0 {
        (0..total)
            .map(|axis| {
                let mut v = crate::ratio::linear::vector::zeros(total);
                v[axis] = Rat::one();
                v
            })
            .collect()
    } else {
        rows.kernel_basis()?
    };
    let projected: Vec<Vec<Rat>> = solutions
        .into_iter()
        .map(|v| v[..keep].to_vec())
        .filter(|v| !is_zero(v))
        .collect();
    annihilator(keep, &projected)
}

/// Where one port's flow and effort land among the elimination variables, with a sign on the flow.
#[derive(Clone, Copy)]
struct Placement {
    flow: usize,
    effort: usize,
    flow_sign: i8,
}

/// The constraint rows of `form`, re-expressed over `variables` columns through a placement per
/// port.
fn placed_rows(
    form: &KernelForm,
    placements: &[Placement],
    variables: usize,
) -> Result<ExactRatMatrix, HolonError> {
    let n = form.ports;
    let rows = form.constraints();
    let mut out = vec![vec![Rat::zero(); variables]; rows.rows()];
    for (row, target) in out.iter_mut().enumerate() {
        for (port, placement) in placements.iter().enumerate() {
            let f = at(rows, row, port);
            let e = at(rows, row, n + port);
            if placement.flow_sign < 0 {
                target[placement.flow] -= f;
            } else {
                target[placement.flow] += f;
            }
            target[placement.effort] += e;
        }
    }
    Ok(matrix(rows.rows(), variables, |row, column| {
        out[row][column].clone()
    })?)
}

/// [definition] How a Dirac structure was presented. Provenance only: identity is the canonical
/// kernel form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DiracPresentation {
    /// `{(J e, e)}` with `Jᵀ = −J`.
    SkewGraph { structure: ExactRatMatrix },
    /// KCL `dᵀ f = 0`, KVL `e = d φ`, with the cycle matrix built for its kernel form.
    Kirchhoff {
        incidence: ExactRatMatrix,
        cycles: ExactRatMatrix,
    },
    /// `{(f, e) | F f + E e = 0}` as declared.
    KernelForm,
    /// `{(0, e)}`: zero flow, every effort.
    PassiveCoholon,
    /// Composed with a link on internal ports.
    Composition,
    /// Interconnected at shared ports.
    Interconnection,
    /// Pushed forward along a port map.
    Pushforward,
    /// Ports relabelled.
    Relabelled,
}

/// [definition] **A certified Dirac structure** (`Holon/Dirac.IsDirac`): a kernel form that
/// passed `F Eᵀ + E Fᵀ = 0` and `rank [F | E] = n`, with its presentation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DiracStructure {
    presentation: DiracPresentation,
    form: KernelForm,
}

impl DiracStructure {
    fn certified(form: KernelForm, presentation: DiracPresentation) -> Result<Self, HolonError> {
        form.certify_dirac()?;
        Ok(Self { presentation, form })
    }

    /// [definition] **The skew graph** `{(J e, e)}` (`Holon/Dirac.skewGraph`), refusing a
    /// non-skew `J` (`Holon/Dirac.identity_graph_not_dirac`).
    pub fn skew_graph(structure: &ExactRatMatrix) -> Result<Self, HolonError> {
        if !structure.is_square() {
            return Err(HolonError::Shape {
                what: "skew structure columns",
                expected: structure.rows(),
                found: structure.columns(),
            });
        }
        if !is_skew(structure) {
            return Err(HolonError::NotSkew);
        }
        // `[1 | −J]` is already in reduced row echelon form (its pivots are the identity block),
        // so it is the canonical kernel form (`Holon/Dirac.skewGraph_eq_kernelForm`) with no
        // elimination.
        let n = structure.rows();
        let form = KernelForm {
            ports: n,
            constraints: hstack(
                &ExactRatMatrix::identity(n)?,
                &structure.scaled(&-Rat::one()),
            )?,
        };
        Self::certified(
            form,
            DiracPresentation::SkewGraph {
                structure: structure.clone(),
            },
        )
    }

    /// [definition] **The Kirchhoff–Stokes–Dirac structure** of an incidence `d : edges × nodes`
    /// (`Holon/Dirac.kirchhoff`), Dirac for every `d` (`Holon/Dirac.kirchhoff_isDirac`).
    pub fn kirchhoff(incidence: &ExactRatMatrix) -> Result<Self, HolonError> {
        let (form, cycles) = KernelForm::from_incidence(incidence)?;
        Self::certified(
            form,
            DiracPresentation::Kirchhoff {
                incidence: incidence.clone(),
                cycles,
            },
        )
    }

    /// [definition] **A declared kernel form**, admitted only when it is Dirac
    /// (`Holon/Dirac.kernelForm_isDirac`); `Holon/Dirac.zero_not_dirac` is the
    /// not-maximal refusal.
    pub fn kernel_form(flow: &ExactRatMatrix, effort: &ExactRatMatrix) -> Result<Self, HolonError> {
        Self::certified(
            KernelForm::new(flow, effort)?,
            DiracPresentation::KernelForm,
        )
    }

    /// [definition] **The passive coholon** `{(0, e)}` (`Holon/Law.passiveCoholon`,
    /// `Holon/Law.passiveCoholon_isDirac`).
    pub fn passive_coholon(ports: usize) -> Result<Self, HolonError> {
        let form = KernelForm::new(
            &ExactRatMatrix::identity(ports)?,
            &ExactRatMatrix::zero(ports, ports)?,
        )?;
        Self::certified(form, DiracPresentation::PassiveCoholon)
    }

    pub fn ports(&self) -> usize {
        self.form.ports
    }

    pub fn form(&self) -> &KernelForm {
        &self.form
    }

    pub fn presentation(&self) -> &DiracPresentation {
        &self.presentation
    }

    pub fn contains(&self, bond: &Bond) -> Result<bool, HolonError> {
        self.form.contains(bond)
    }

    pub fn basis(&self) -> Result<Vec<Bond>, HolonError> {
        self.form.basis()
    }

    /// The same subspace as another structure.
    pub fn same_subspace(&self, other: &Self) -> bool {
        self.form.same_subspace(&other.form)
    }

    /// [definition] **Tellegen on the structure**: every pair of basis bonds pairs to zero, so
    /// every admitted bond carries zero power (`Holon/Dirac.IsDirac.pairing_eq_zero`).
    /// Returns the number of pairings checked; a nonzero pairing is a refusal.
    pub fn tellegen(&self) -> Result<usize, HolonError> {
        let basis = self.basis()?;
        let mut checked = 0;
        for (index, left) in basis.iter().enumerate() {
            for right in &basis[index..] {
                if !left.pairing(right)?.is_zero() {
                    return Err(HolonError::NotIsotropic);
                }
                checked += 1;
            }
        }
        Ok(checked)
    }

    /// [definition] **Composition through a link** (`Holon/Dirac.compose`): the ports listed
    /// in `internal` form `Q`; the result is `{p | ∃ q ∈ link, (p, q) ∈ self}` on the remaining
    /// ports in their order. Dirac by `Holon/Dirac.compose_isDirac`, re-certified here.
    pub fn compose(&self, link: &Self, internal: &[usize]) -> Result<Self, HolonError> {
        let n = self.ports();
        check_distinct(internal, n)?;
        if link.ports() != internal.len() {
            return Err(HolonError::Shape {
                what: "link ports",
                expected: internal.len(),
                found: link.ports(),
            });
        }
        let outer: Vec<usize> = (0..n).filter(|port| !internal.contains(port)).collect();
        let (m, t) = (outer.len(), internal.len());
        let variables = 2 * m + 2 * t;
        let mut placements = vec![
            Placement {
                flow: 0,
                effort: 0,
                flow_sign: 1
            };
            n
        ];
        for (position, port) in outer.iter().enumerate() {
            placements[*port] = Placement {
                flow: position,
                effort: m + position,
                flow_sign: 1,
            };
        }
        let shared: Vec<Placement> = (0..t)
            .map(|k| Placement {
                flow: 2 * m + k,
                effort: 2 * m + t + k,
                flow_sign: 1,
            })
            .collect();
        for (k, port) in internal.iter().enumerate() {
            placements[*port] = shared[k];
        }
        let rows = vstack(
            &placed_rows(&self.form, &placements, variables)?,
            &placed_rows(&link.form, &shared, variables)?,
        )?;
        let form = KernelForm::from_constraints(m, &eliminate(&rows, 2 * m)?)?;
        Self::certified(form, DiracPresentation::Composition)
    }

    /// [definition] **Interconnection at shared ports** (`Holon/Dirac.interconnect`): each
    /// `(a, b)` in `joined` identifies port `a` of `self` with port `b` of `other`, flows opposite
    /// and efforts equal (`Holon/Dirac.link`). The result's ports are `self`'s unjoined ports
    /// then `other`'s, each in order. A bond is admitted exactly when some shared bond `q` admits
    /// both sides (`Holon/Dirac.mem_interconnect`); the result is Dirac
    /// (`Holon/Dirac.interconnect_isDirac`), re-certified here.
    pub fn interconnect(
        &self,
        other: &Self,
        joined: &[(usize, usize)],
    ) -> Result<Self, HolonError> {
        let left: Vec<usize> = joined.iter().map(|(a, _)| *a).collect();
        let right: Vec<usize> = joined.iter().map(|(_, b)| *b).collect();
        check_distinct(&left, self.ports())?;
        check_distinct(&right, other.ports())?;
        let a_free: Vec<usize> = (0..self.ports()).filter(|p| !left.contains(p)).collect();
        let b_free: Vec<usize> = (0..other.ports()).filter(|p| !right.contains(p)).collect();
        let (m, t) = (a_free.len() + b_free.len(), joined.len());
        let variables = 2 * m + 2 * t;
        let blank = Placement {
            flow: 0,
            effort: 0,
            flow_sign: 1,
        };
        let mut a_place = vec![blank; self.ports()];
        for (position, port) in a_free.iter().enumerate() {
            a_place[*port] = Placement {
                flow: position,
                effort: m + position,
                flow_sign: 1,
            };
        }
        let mut b_place = vec![blank; other.ports()];
        for (position, port) in b_free.iter().enumerate() {
            let at = a_free.len() + position;
            b_place[*port] = Placement {
                flow: at,
                effort: m + at,
                flow_sign: 1,
            };
        }
        for (k, (a, b)) in joined.iter().enumerate() {
            a_place[*a] = Placement {
                flow: 2 * m + k,
                effort: 2 * m + t + k,
                flow_sign: 1,
            };
            b_place[*b] = Placement {
                flow: 2 * m + k,
                effort: 2 * m + t + k,
                flow_sign: -1,
            };
        }
        let rows = vstack(
            &placed_rows(&self.form, &a_place, variables)?,
            &placed_rows(&other.form, &b_place, variables)?,
        )?;
        let form = KernelForm::from_constraints(m, &eliminate(&rows, 2 * m)?)?;
        Self::certified(form, DiracPresentation::Interconnection)
    }

    /// [definition] **The pushforward along a port map** `P : ports → ports'`
    /// (`Holon/Restriction.pushforwardD`): `{(f', e') | ∃ f, P f = f', (f, Pᵀ e') ∈ self}`
    /// (`Holon/Restriction.mem_pushforwardD`); Dirac for every `P`
    /// (`Holon/Restriction.pushforwardD_isDirac`), re-certified here.
    pub fn pushforward(&self, map: &ExactRatMatrix) -> Result<Self, HolonError> {
        let n = self.ports();
        if map.columns() != n {
            return Err(HolonError::Shape {
                what: "port map columns",
                expected: n,
                found: map.columns(),
            });
        }
        let m = map.rows();
        // Variables: f' (m), e' (m), f (n).
        let variables = 2 * m + n;
        let flow = self.form.flow_matrix()?;
        let effort = self.form.effort_matrix()?;
        let effort_through = effort.multiply(&map.transpose()?)?;
        let k = self.form.rank();
        let mut rows = vec![vec![Rat::zero(); variables]; m + k];
        for (row, target) in rows.iter_mut().enumerate().take(m) {
            target[row] = -Rat::one();
            for column in 0..n {
                target[2 * m + column] = at(map, row, column);
            }
        }
        for row in 0..k {
            let target = &mut rows[m + row];
            for column in 0..m {
                target[m + column] = at(&effort_through, row, column);
            }
            for column in 0..n {
                target[2 * m + column] = at(&flow, row, column);
            }
        }
        let rows = matrix(m + k, variables, |row, column| rows[row][column].clone())?;
        let form = KernelForm::from_constraints(m, &eliminate(&rows, 2 * m)?)?;
        Self::certified(form, DiracPresentation::Pushforward)
    }

    /// [definition] **Relabel ports** (`Holon/Dirac.bondReindex`): new port `i` is old port
    /// `order[i]`. Refuses a non-permutation.
    pub fn relabel(&self, order: &[usize]) -> Result<Self, HolonError> {
        let n = self.ports();
        if order.len() != n {
            return Err(HolonError::NotPermutation);
        }
        check_distinct(order, n).map_err(|_| HolonError::NotPermutation)?;
        let flow = select_columns(&self.form.flow_matrix()?, order)?;
        let effort = select_columns(&self.form.effort_matrix()?, order)?;
        Self::certified(
            KernelForm::new(&flow, &effort)?,
            DiracPresentation::Relabelled,
        )
    }
}

fn check_distinct(ports: &[usize], extent: usize) -> Result<(), HolonError> {
    for (index, port) in ports.iter().enumerate() {
        if *port >= extent {
            return Err(HolonError::PortOutside {
                port: *port,
                ports: extent,
            });
        }
        if ports[..index].contains(port) {
            return Err(HolonError::PortJoinedTwice { port: *port });
        }
    }
    Ok(())
}

/// [definition] **Tellegen is Stokes** (`Holon/Dirac.tellegen`): returns `(⟨dφ, f⟩, ⟨φ, dᵀf⟩)`,
/// which are equal for every incidence, potential and flow.
pub fn tellegen(
    incidence: &ExactRatMatrix,
    potential: &[Rat],
    flow: &[Rat],
) -> Result<(Rat, Rat), HolonError> {
    let drops = incidence.apply(potential)?;
    let boundary = incidence.transpose()?.apply(flow)?;
    Ok((dot(&drops, flow), dot(potential, &boundary)))
}

/// Membership in the Kirchhoff structure read directly: KCL `dᵀ f = 0` and KVL `e ∈ range d`.
pub fn kirchhoff_admits(incidence: &ExactRatMatrix, bond: &Bond) -> Result<bool, HolonError> {
    if bond.ports() != incidence.rows() {
        return Err(HolonError::Shape {
            what: "Kirchhoff bond",
            expected: incidence.rows(),
            found: bond.ports(),
        });
    }
    let kcl = is_zero(&incidence.transpose()?.apply(bond.flow())?);
    Ok(kcl && incidence.preimage_fibre(bond.effort())?.is_some())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::linear::vector::{integer_matrix, ints};

    fn gyrator() -> ExactRatMatrix {
        integer_matrix(&[&[0, -1], &[1, 0]]).unwrap()
    }

    fn triangle() -> ExactRatMatrix {
        integer_matrix(&[&[-1, 1, 0], &[0, -1, 1], &[1, 0, -1]]).unwrap()
    }

    /// `Holon/Dirac.gyrator_witness`.
    #[test]
    fn a_gyrator_bond_moves_and_carries_no_power() {
        let d = DiracStructure::skew_graph(&gyrator()).unwrap();
        let bond = Bond::new(ints(&[-1, 1]), ints(&[1, 1])).unwrap();
        assert!(d.contains(&bond).unwrap());
        assert!(bond.power().is_zero());
        assert_eq!(d.tellegen().unwrap(), 3);
    }

    /// `Holon/Dirac.identity_graph_not_dirac` and `Holon/Dirac.zero_not_dirac`.
    #[test]
    fn a_non_skew_graph_and_the_zero_subspace_are_refused() {
        assert_eq!(
            DiracStructure::skew_graph(&ExactRatMatrix::identity(2).unwrap()),
            Err(HolonError::NotSkew)
        );
        let zero = KernelForm::new(
            &integer_matrix(&[&[1, 0], &[0, 1], &[0, 0], &[0, 0]]).unwrap(),
            &integer_matrix(&[&[0, 0], &[0, 0], &[1, 0], &[0, 1]]).unwrap(),
        )
        .unwrap();
        assert_eq!(zero.dimension(), 0);
        assert!(zero.is_isotropic().unwrap());
        assert_eq!(
            zero.certify_dirac(),
            Err(HolonError::NotMaximal { rank: 4, ports: 2 })
        );
        // The orthogonal of the zero subspace is everything.
        assert_eq!(zero.orthogonal().unwrap().dimension(), 4);
    }

    /// `Holon/Dirac.triangle_witness` and `Holon/Dirac.triangle_kernelForm`.
    #[test]
    fn the_triangle_carries_a_loop_current_against_a_potential() {
        let d = DiracStructure::kirchhoff(&triangle()).unwrap();
        let bond = Bond::new(ints(&[1, 1, 1]), ints(&[1, 2, -3])).unwrap();
        assert!(d.contains(&bond).unwrap());
        assert!(kirchhoff_admits(&triangle(), &bond).unwrap());
        assert!(bond.power().is_zero());
        let DiracPresentation::Kirchhoff { cycles, .. } = d.presentation() else {
            panic!("presentation");
        };
        assert_eq!(cycles.columns(), 1);
        // The declared triangle kernel form, loop (1,1,1), is the same subspace.
        let flow = vstack(
            &triangle().transpose().unwrap(),
            &ExactRatMatrix::zero(1, 3).unwrap(),
        )
        .unwrap();
        let effort = vstack(
            &ExactRatMatrix::zero(3, 3).unwrap(),
            &integer_matrix(&[&[1, 1, 1]]).unwrap(),
        )
        .unwrap();
        let declared = DiracStructure::kernel_form(&flow, &effort).unwrap();
        assert!(declared.same_subspace(&d));
        let (drop_pairing, boundary_pairing) =
            tellegen(&triangle(), &ints(&[0, 1, 3]), &ints(&[2, -1, 5])).unwrap();
        assert_eq!(drop_pairing, boundary_pairing);
    }

    /// `Holon/Dirac.gyrator_chain_witness`: two gyrators interconnected are a transformer.
    #[test]
    fn two_gyrators_interconnected_are_a_transformer() {
        let g = DiracStructure::skew_graph(&gyrator()).unwrap();
        let chain = g.interconnect(&g, &[(1, 0)]).unwrap();
        let bond = Bond::new(ints(&[1, -1]), ints(&[2, 2])).unwrap();
        assert!(chain.contains(&bond).unwrap());
        assert!(bond.power().is_zero());
        // The shared bond (f_s, e_s) = (2, −1) admits both sides (mem_interconnect).
        let a_side = Bond::new(ints(&[1, 2]), ints(&[2, -1])).unwrap();
        let b_side = Bond::new(ints(&[-2, -1]), ints(&[-1, 2])).unwrap();
        assert!(g.contains(&a_side).unwrap());
        assert!(g.contains(&b_side).unwrap());
        assert_eq!(a_side.power() + b_side.power(), bond.power());
        // The composite is the same as composing the paired structure with the link.
        let paired = g.interconnect(&g, &[]).unwrap();
        // The two-port link (Holon/Dirac.link): flows opposite, efforts equal.
        let link = DiracStructure::kernel_form(
            &integer_matrix(&[&[1, 1], &[0, 0]]).unwrap(),
            &integer_matrix(&[&[0, 0], &[1, -1]]).unwrap(),
        )
        .unwrap();
        let composed = paired.compose(&link, &[1, 2]).unwrap();
        assert!(composed.same_subspace(&chain));
        assert_eq!(chain.form().certify_dirac(), Ok(()));
    }

    /// `Holon/Restriction.gyrator_projection_witness`.
    #[test]
    fn pushing_the_gyrator_along_a_projection_gives_the_passive_coholon() {
        let g = DiracStructure::skew_graph(&gyrator()).unwrap();
        let pushed = g.pushforward(&integer_matrix(&[&[1, 0]]).unwrap()).unwrap();
        assert!(pushed.same_subspace(&DiracStructure::passive_coholon(1).unwrap()));
    }

    #[test]
    fn relabelling_preserves_dirac_and_refuses_a_non_permutation() {
        let d = DiracStructure::kirchhoff(&triangle()).unwrap();
        let r = d.relabel(&[2, 0, 1]).unwrap();
        let bond = Bond::new(ints(&[1, 1, 1]), ints(&[-3, 1, 2])).unwrap();
        assert!(r.contains(&bond).unwrap());
        assert_eq!(d.relabel(&[0, 0, 1]), Err(HolonError::NotPermutation));
        assert_eq!(r.form().orthogonal().unwrap(), r.form().clone());
    }
}
