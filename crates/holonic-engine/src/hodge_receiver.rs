//! **The Hodge and spectral receiver on an incidence complex.**
//!
//! [definition] This is receiver **R3** of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`. It builds
//!
//! ```text
//! Δ_k = d_{k−1} d_{k−1}^* + d_k^* d_k
//! ```
//!
//! over the incidence complex that [`crate::physical_constraint_grading`] returns, under a
//! **declared** metric and **declared** boundary conditions, and exposes the Hodge decomposition
//! of a cochain, the harmonic dimension against Betti from Smith normal form, the spectrum held
//! exactly, the spectral gap as an exact interval, and mode localization.
//!
//! # Nothing here is a default
//!
//! [definition] The metric is a [`MetricDeclaration`] and the unit metric is
//! [`MetricLaw::Unit`] — **one declaration among others, not the absence of one**. A bare
//! transpose is the codifferential only under an undeclared orthonormal chart, which is exactly
//! the substitution [`crate::exact_linear::ExactRatMatrix::metric_adjoint`] exists to refuse; this
//! module reaches the codifferential `δ_k = W_k^{-1} d_k^T W_{k+1}` through that owner and never
//! writes a transpose in its place. The boundary condition is a [`BoundaryCondition`]:
//! [`BoundaryCondition::Free`] is the absolute complex, named; [`BoundaryCondition::VanishingOn`]
//! is the relative complex `C^*(K, L)` for a declared subcomplex `L`, refused by name unless `L`
//! really is closed under boundary. There is no third, implicit option.
//!
//! # What is cited rather than rebuilt
//!
//! | This module needs | The owner it uses |
//! |---|---|
//! | the exact cellular coboundary | [`crate::sheaf_diffusion::ExactCellularSheaf::coboundary`] (`sheaf_diffusion.rs:274`) through the rank-one sheaf on the same complex |
//! | the unit-metric Hodge operator to agree with, entry for entry | [`crate::sheaf_diffusion::ExactCellularSheaf::hodge_laplacian`] (`:307`), checked in `the_coboundary_and_the_unit_laplacian_agree_with_the_cellular_sheaf_owner` |
//! | the metric adjoint | [`crate::exact_linear::ExactRatMatrix::metric_adjoint`] (`exact_linear.rs:987`) and [`crate::exact_linear::ExactRatMatrix::adjoint_defect`] (`:1006`) |
//! | rank, kernel, image, preimage fibre | `exact_linear.rs:761,770,796,823` |
//! | Betti numbers with torsion | [`crate::rebase_invariants::smith_normal_form`] (`rebase_invariants.rs:440`), cross-checked against [`crate::rebase_invariants::rebase_invariants`] (`:723`) |
//! | the characteristic polynomial over `ℚ` | [`crate::lattice_gauge::characteristic_polynomial`] (`lattice_gauge.rs:946`) |
//! | squarefree factorization with multiplicities | [`crate::rational_polynomial::RationalPolynomial::squarefree_decomposition`] |
//! | every rational eigenvalue, completely | [`crate::rational_polynomial::rational_roots_by_lifting`] |
//! | the Sturm root count and the isolation certificate | [`crate::exact_value::IntegerPolynomial::distinct_root_count`] and [`crate::exact_value::AlgebraicRoot::isolate`] |
//!
//! [definition] **Where the isolation lives, and what this receiver contributes to it.**
//! [`crate::lattice_gauge::exact_spectrum`] answers the same question and its rational half is used
//! here in the form of `rational_roots_by_lifting`, the fast route that module's own head
//! recommends. Its *isolation* half used to descend from the absolute Cauchy bound
//! `max |coefficient| + 1` of the monic companion, which for a Hodge Laplacian is astronomically
//! wider than the spectrum — so this module carried its own descent from the bound
//! positive semidefiniteness gives it. **That is no longer a second descent.**
//! [`crate::rational_polynomial::isolate_against_chain`] takes a declared enclosure as a
//! first-class argument and does the bisection against one cached
//! [`crate::exact_value::SturmChain`]; what this receiver contributes is the enclosure itself,
//! `Δ_k` being positive semidefinite in the declared metric so that **every eigenvalue lies in
//! `[0, tr Δ_k]`**. One chain is built per reading and every count below — the isolation, the
//! certificates, [`refine_spectral_gap`] — is taken against it.
//!
//! # The three-way decomposition, exactly
//!
//! [proved-derived; implemented-exact] With `⟪x,y⟫_k = Σ w(c) x_c y_c` for declared positive
//! rational weights `w`, `im d_{k−1}`, `im d_k^*` and `ker Δ_k` are pairwise orthogonal and span
//! `C^k`. [`hodge_decomposition`] returns the three components as exact rationals, computed as the
//! `W`-orthogonal projections `B (Bᵀ W B)^{-1} Bᵀ W` onto exhibited bases, and **re-derives at
//! every reading** that the three sum back to the input, that the three pairings vanish and that
//! the harmonic part is annihilated by `Δ_k`, by `d_k` and by `d_{k−1}^*` separately. Nothing is
//! asserted: [`HodgeError::DecompositionDoesNotSum`], [`HodgeError::ComponentsNotOrthogonal`] and
//! [`HodgeError::HarmonicNotAnnihilated`] are the refusals.
//!
//! [proved-standard] `dim ker Δ_k = n_k − rank d_k − rank d_{k−1}` is the free rank of the `k`-th
//! cohomology over `ℚ`, and [`hodge_reading`] refuses unless it agrees with the Betti number the
//! Smith normal form returns over `ℤ` ([`HodgeError::HarmonicDimensionDisagreesWithBetti`]). The
//! two computations share no code: one is a rational row reduction, the other an integer
//! elimination with divisibility repair. **Torsion is recorded and is not seen by the harmonic
//! space** — the rational Hodge theory reads the free rank only, and
//! [`HodgeReading::torsion`] is retained so that this is visible rather than lost.
//!
//! # The spectrum is held, never approximated
//!
//! [implemented-exact] [`exact_hodge_spectrum`] returns the characteristic polynomial over `ℚ`,
//! its squarefree decomposition keyed by multiplicity, every rational eigenvalue with its
//! multiplicity, and every irrational eigenvalue as an [`crate::exact_value::AlgebraicRoot`] —
//! a polynomial plus a rational interval plus the Sturm sign-variation certificate that the
//! interval holds exactly one root. The spectral gap is an [`crate::exact_value::ExactInterval`]
//! and is a point interval exactly when the smallest positive eigenvalue is rational. **No float
//! appears anywhere on this path**, including in the gap.
//!
//! [proved-derived] Two facts about `Δ_k` make the isolation complete rather than a search:
//! it is self-adjoint in the declared inner product, so its spectrum is real, and it is positive
//! semidefinite, so the spectrum lies in `[0, tr Δ_k]`. The reading refuses with
//! [`HodgeError::SpectrumIncomplete`] if the isolated population does not account for every
//! distinct root of the squarefree part, which is what would happen if either fact failed.
//!
//! # Mode localization
//!
//! [implemented-exact] For a **rational** eigenvalue the eigenspace is exhibited exactly:
//! [`ModeLocalization::support`] is the set of cells at which some eigenvector is nonzero — a
//! property of the subspace and not of the basis — and [`ModeLocalization::participation`] is the
//! exact rational participation ratio `(Σ w v²)² / Σ w² v⁴` of each vector of the canonical
//! reduced-echelon kernel basis, which is basis-dependent and is said so here.
//!
//! [proved-derived] For an **irrational** eigenvalue the statement is interval-certified instead.
//! `Δ_k`'s nonzero off-diagonal pattern decomposes the coordinates into decoupled blocks; the
//! characteristic polynomial is exactly the product of the blocks' (checked, not assumed:
//! [`HodgeError::BlockProductDisagrees`]), so every eigenvector for an eigenvalue `λ` is supported
//! inside the union of the blocks whose own characteristic polynomial vanishes at `λ`. Which
//! blocks those are is decided exactly by the signs of each block's **squarefree part** at the two
//! rational endpoints of the isolating interval: the squarefree part has at most one, simple, root
//! there, so a sign change is the root. No endpoint is ever a root, because the isolation splits
//! away from the exactly known rational root population.
//!
//! # The Open-contact family is carried
//!
//! [definition] `physical_constraint_grading` returns a family because an `Open` contact is a
//! 1-cell that may or may not exist. Different resolutions give different complexes, hence
//! different `Δ_k`, hence different spectra. [`hodge_family`] reads **each bound** and returns a
//! family of readings; [`HodgeFamily::bounds_differ_spectrally`] says on the actual data whether
//! the open class is a spectral question. It is answered affirmatively on a worked presentation
//! whose two bounds have **equal Betti numbers** — the open contact is invisible to homology and
//! visible to the spectrum. That is the separation this receiver exists for.
//!
//! # Formal owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/HodgeReceiver.lean`, namespace
//! `Soma.Holonics.Foundation.HodgeReceiver`. The correspondence, both directions:
//!
//! | Rust | Lean |
//! |---|---|
//! | [`MetricLaw`] with positive rational weights | `WeightedComplex.w₀/w₁/w₂` with `w₀pos`/`w₁pos`/`w₂pos` |
//! | [`MetricLaw::Unit`] as one declaration among others | `unitMetric`, and `unitMetric_codiff₀` — the only place a bare transpose *is* the codifferential |
//! | [`HodgeOperator::inner`] | `ip`, `ip_symm`, `ip_self_nonneg`, `ip_eq_zero` |
//! | [`HodgeOperator::codifferential`] | `WeightedComplex.codiff₀/codiff₁` |
//! | the adjoint law checked in [`HodgeOperator::validate`] | `codiff₀_adjoint`, `codiff₁_adjoint` |
//! | `d ∘ d = 0` checked in [`HodgeOperator::validate`] | `WeightedComplex.dd` |
//! | [`HodgeOperator::laplacian`] | `WeightedComplex.laplacian` |
//! | `Δ` self-adjoint | `laplacian_selfAdjoint` |
//! | `⟪Δx,x⟫ ≥ 0`, and the exact identity it comes from | `laplacian_quadratic`, `laplacian_posSemidef` |
//! | `ker Δ = ker d_k ∩ ker d_{k−1}^*` | `mem_harmonic_iff` |
//! | the three-way orthogonal decomposition | `hodge_decomposition`, `hodge_decomposition_unique`, `harmonic_eq_orthogonal` |
//! | the pairwise orthogonality re-derived at every reading | `exact_orthogonal_coexact`, `harmonic_orthogonal_exact`, `harmonic_orthogonal_coexact` |
//! | harmonic dimension = Betti | `finrank_harmonic_add_finrank_exact`, `harmonicEquivCohomology`, `cocycles_eq_sup` |
//! | metric change moves the representative, not the dimension | `harmonic_moves_within_class`, `finrank_harmonic_metric_free` |
//!
//! Every one of those elaborates with `#print axioms` returning
//! `[propext, Classical.choice, Quot.sound]` and no `sorryAx`.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::algebraic::{CausalAlgebraicError, CausalCellId, GradedCausalComplex};
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::exact_value::{AlgebraicRoot, ExactInterval, ExactValueError, IntegerPolynomial, SturmChain};
use crate::lattice_gauge::{LatticeGaugeRefusal, characteristic_polynomial};
use crate::physical_constraint_complex::{ConstraintVertexId, PhysicalConstraintComplex};
use crate::physical_constraint_grading::{
    ConstraintGradingError, ConstraintComplexFamily, GradedConstraintComplex, OpenContact,
    OpenContactLaw, graded_constraint_family, graded_constraint_member,
};
use crate::rational_polynomial::{
    ExactPolynomialError, RationalPolynomial, isolate_against_chain, rational_roots_by_lifting,
};
use crate::rebase_invariants::{IntegerMatrix, PivotRule, smith_normal_form};

// -------------------------------------------------------------------------------------------
// the declared metric
// -------------------------------------------------------------------------------------------

/// **How the metric weight of a cell is declared.**
///
/// [definition] There is no default. [`MetricLaw::Unit`] is a *declaration* that every cell
/// carries weight one; it is written down like any other, and a caller that wants it says so.
///
/// **A remounted law is refused when it declares a weight that is not a weight.** Positivity is the
/// one thing a law states without reference to any population — a metric is positive definite or it
/// is not a metric — and [`CellMetric::resolve`] already refuses a non-positive per-grade weight, so
/// the wire refuses it at the declaration instead of letting one travel to the first resolution
/// that happens to name that grade.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "MetricLawWire")]
pub enum MetricLaw {
    /// Every cell carries weight one.
    Unit,
    /// Every cell of grade `g` carries the weight declared at `g`. Every grade the active
    /// population reaches must be named, and every named weight must be positive.
    PerGrade(BTreeMap<u32, Rat>),
    /// Every cell carries its own declared weight. Names exactly the active cells, and is
    /// **member-local**: cell addresses are founded per member of an open family, so this law
    /// cannot be carried across a family and [`hodge_family`] refuses it by name.
    PerCell(BTreeMap<CausalCellId, Rat>),
}

#[derive(Deserialize)]
enum MetricLawWire {
    Unit,
    PerGrade(BTreeMap<u32, Rat>),
    PerCell(BTreeMap<CausalCellId, Rat>),
}

/// The lineage a refusal names when the malformed weight is in a bare law, which carries none.
const REMOUNTED_LAW_LINEAGE: &str = "a remounted metric law";

impl TryFrom<MetricLawWire> for MetricLaw {
    type Error = HodgeError;

    fn try_from(wire: MetricLawWire) -> Result<Self, Self::Error> {
        match wire {
            MetricLawWire::Unit => Ok(Self::Unit),
            MetricLawWire::PerGrade(declared) => {
                for (grade, weight) in &declared {
                    if !weight.is_positive() {
                        return Err(HodgeError::MetricWeightNotPositive {
                            lineage: REMOUNTED_LAW_LINEAGE.to_owned(),
                            cell: None,
                            grade: Some(*grade),
                        });
                    }
                }
                Ok(Self::PerGrade(declared))
            }
            MetricLawWire::PerCell(declared) => {
                for (cell, weight) in &declared {
                    if !weight.is_positive() {
                        return Err(HodgeError::MetricWeightNotPositive {
                            lineage: REMOUNTED_LAW_LINEAGE.to_owned(),
                            cell: Some(*cell),
                            grade: None,
                        });
                    }
                }
                Ok(Self::PerCell(declared))
            }
        }
    }
}

impl MetricLaw {
    /// Whether this law names cells rather than grades, and therefore cannot cross a family.
    pub fn is_member_local(&self) -> bool {
        matches!(self, Self::PerCell(_))
    }
}

/// A named metric law, before it is resolved against a cell population.
///
/// **Its wire adds nothing beyond its law's.** The lineage is a free declaration and the law is
/// closed at [`MetricLaw`]'s own wire, so there is no relation left between the two fields to
/// check. Everything else a declaration claims is claimed about a population it has not met, and
/// [`CellMetric::resolve`] is where it meets one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MetricDeclaration {
    pub lineage: String,
    pub law: MetricLaw,
}

impl MetricDeclaration {
    /// The unit metric, declared. Not a default: this call is the declaration.
    pub fn unit(lineage: impl Into<String>) -> Self {
        Self {
            lineage: lineage.into(),
            law: MetricLaw::Unit,
        }
    }

    pub fn per_grade(
        lineage: impl Into<String>,
        weights: impl IntoIterator<Item = (u32, Rat)>,
    ) -> Self {
        Self {
            lineage: lineage.into(),
            law: MetricLaw::PerGrade(weights.into_iter().collect()),
        }
    }

    pub fn per_cell(
        lineage: impl Into<String>,
        weights: impl IntoIterator<Item = (CausalCellId, Rat)>,
    ) -> Self {
        Self {
            lineage: lineage.into(),
            law: MetricLaw::PerCell(weights.into_iter().collect()),
        }
    }
}

/// The metric resolved against one cell population: an exact positive rational per active cell.
///
/// **A remounted metric is held to its own law.** Every resolved weight must be positive, and where
/// the law decides the resolution without the population — a unit law resolves to the constant one,
/// a per-cell law resolves to exactly the map it declares — the resolution is re-derived from the
/// law and refused on disagreement. A per-grade law does not decide it without the cell grades,
/// which this struct does not carry, so there only the weaker relation is checkable: every resolved
/// weight is one of the declared per-grade weights. Whether the resolution *covers* the active
/// population is a statement about the complex, and [`HodgeOperator::validate`] re-derives it at
/// every reading.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CellMetricWire")]
pub struct CellMetric {
    pub lineage: String,
    pub law: MetricLaw,
    weights: BTreeMap<CausalCellId, Rat>,
}

#[derive(Deserialize)]
struct CellMetricWire {
    lineage: String,
    law: MetricLaw,
    weights: BTreeMap<CausalCellId, Rat>,
}

impl TryFrom<CellMetricWire> for CellMetric {
    type Error = HodgeError;

    fn try_from(wire: CellMetricWire) -> Result<Self, Self::Error> {
        for (cell, weight) in &wire.weights {
            if !weight.is_positive() {
                return Err(HodgeError::MetricWeightNotPositive {
                    lineage: wire.lineage.clone(),
                    cell: Some(*cell),
                    grade: None,
                });
            }
        }
        match &wire.law {
            MetricLaw::Unit => {
                for (cell, weight) in &wire.weights {
                    if !weight.is_one() {
                        return Err(HodgeError::HodgeWireDisagrees {
                            object: "resolved metric",
                            relation: "a unit law's resolved weight",
                            declared: format!("{weight} at {cell:?}"),
                            derived: "1".to_owned(),
                        });
                    }
                }
            }
            MetricLaw::PerCell(declared) => {
                if *declared != wire.weights {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "resolved metric",
                        relation: "a per-cell law's resolution, which is the declaration itself",
                        declared: declared.len().to_string(),
                        derived: wire.weights.len().to_string(),
                    });
                }
            }
            MetricLaw::PerGrade(declared) => {
                for (cell, weight) in &wire.weights {
                    if !declared.values().any(|value| value == weight) {
                        return Err(HodgeError::HodgeWireDisagrees {
                            object: "resolved metric",
                            relation: "a resolved weight against the per-grade weights declared",
                            declared: format!("{weight} at {cell:?}"),
                            derived: "one of the declared per-grade weights".to_owned(),
                        });
                    }
                }
            }
        }
        Ok(Self {
            lineage: wire.lineage,
            law: wire.law,
            weights: wire.weights,
        })
    }
}

impl CellMetric {
    /// Resolve a declaration against the active cells of a complex.
    ///
    /// Refuses a non-positive weight, an unnamed grade, an unnamed cell and a named cell that is
    /// not active — each by name. A metric that does not cover the population is not a metric.
    pub fn resolve(
        declaration: &MetricDeclaration,
        complex: &GradedCausalComplex,
        active: &BTreeSet<CausalCellId>,
    ) -> Result<Self, HodgeError> {
        let mut weights = BTreeMap::new();
        match &declaration.law {
            MetricLaw::Unit => {
                for cell in active {
                    weights.insert(*cell, Rat::one());
                }
            }
            MetricLaw::PerGrade(declared) => {
                for (grade, weight) in declared {
                    if !weight.is_positive() {
                        return Err(HodgeError::MetricWeightNotPositive {
                            lineage: declaration.lineage.clone(),
                            cell: None,
                            grade: Some(*grade),
                        });
                    }
                }
                for cell in active {
                    let grade = complex.cell(*cell)?.grade;
                    let weight = declared
                        .get(&grade)
                        .ok_or(HodgeError::MetricGradeUnnamed { grade })?;
                    weights.insert(*cell, weight.clone());
                }
            }
            MetricLaw::PerCell(declared) => {
                for cell in active {
                    let weight = declared
                        .get(cell)
                        .ok_or(HodgeError::MetricCellUnnamed(*cell))?;
                    if !weight.is_positive() {
                        return Err(HodgeError::MetricWeightNotPositive {
                            lineage: declaration.lineage.clone(),
                            cell: Some(*cell),
                            grade: None,
                        });
                    }
                    weights.insert(*cell, weight.clone());
                }
                for cell in declared.keys() {
                    if !active.contains(cell) {
                        return Err(HodgeError::MetricNamesInactiveCell(*cell));
                    }
                }
            }
        }
        Ok(Self {
            lineage: declaration.lineage.clone(),
            law: declaration.law.clone(),
            weights,
        })
    }

    pub fn weight(&self, cell: CausalCellId) -> Result<&Rat, HodgeError> {
        self.weights
            .get(&cell)
            .ok_or(HodgeError::MetricCellUnnamed(cell))
    }

    pub fn weights(&self) -> &BTreeMap<CausalCellId, Rat> {
        &self.weights
    }

    /// Whether every active weight is one. A declared unit metric and a declared per-cell metric
    /// that happens to be one are the same operator and different declarations.
    pub fn is_unit_valued(&self) -> bool {
        self.weights.values().all(|weight| weight.is_one())
    }
}

// -------------------------------------------------------------------------------------------
// the declared boundary condition
// -------------------------------------------------------------------------------------------

/// **The declared boundary condition**, resolved to cell addresses.
///
/// **Its one invariant needs a complex, so its wire cannot carry it.** Closure under boundary is a
/// statement about the complex the condition is applied to, which the condition does not carry;
/// [`BoundaryCondition::active`] decides it against the complex at every use, refusing
/// [`HodgeError::BoundarySetNotClosed`] there. A named cell set on its own is a lawful declaration
/// whatever it names, so a wire that re-checked something here would be re-checking nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BoundaryCondition {
    /// Every cell participates: the absolute complex `C^*(K)`. A declaration, named.
    Free,
    /// Cochains vanish on a declared subcomplex `L`: the relative complex `C^*(K, L)`.
    ///
    /// `L` must be closed under boundary, which [`GradedCausalComplex::is_closed_support`]
    /// decides; otherwise this is refused with [`HodgeError::BoundarySetNotClosed`]. Closure is
    /// exactly what makes the coboundary preserve the subspace, so the relative complex really is
    /// the submatrix on `K \ L` and not a truncation.
    VanishingOn {
        lineage: String,
        cells: BTreeSet<CausalCellId>,
    },
}

impl BoundaryCondition {
    pub fn lineage(&self) -> &str {
        match self {
            Self::Free => "free",
            Self::VanishingOn { lineage, .. } => lineage,
        }
    }

    /// The active cells this condition leaves.
    pub fn active(
        &self,
        complex: &GradedCausalComplex,
    ) -> Result<BTreeSet<CausalCellId>, HodgeError> {
        let all: BTreeSet<CausalCellId> = complex.cells().keys().copied().collect();
        match self {
            Self::Free => Ok(all),
            Self::VanishingOn { cells, .. } => {
                for cell in cells {
                    if !all.contains(cell) {
                        return Err(HodgeError::BoundaryCellAbsent(*cell));
                    }
                }
                if !complex.is_closed_support(cells)? {
                    return Err(HodgeError::BoundarySetNotClosed);
                }
                Ok(all.difference(cells).copied().collect())
            }
        }
    }
}

/// **A boundary condition declared by occurrence address rather than by cell address.**
///
/// [definition] Cell addresses are founded per member, so a condition written in them cannot cross
/// an open family. This law names *occurrences*; the subcomplex it resolves to is every cell all
/// of whose vertices are named, which is closed under boundary by construction, and it resolves
/// the same way against every member.
///
/// **Its wire adds nothing.** A set of occurrence addresses is a lawful declaration whatever it
/// names — that is the point of addressing the condition this way — and the subcomplex it resolves
/// to is closed under boundary by construction. [`Self::resolve`] meets a member and
/// [`BoundaryCondition::active`] meets the complex; neither question can be asked here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BoundaryLaw {
    Free,
    VanishingOnOccurrences {
        lineage: String,
        occurrences: BTreeSet<ConstraintVertexId>,
    },
}

impl BoundaryLaw {
    /// The condition this law resolves to against one member of a constraint family.
    pub fn resolve(&self, member: &GradedConstraintComplex) -> Result<BoundaryCondition, HodgeError> {
        match self {
            Self::Free => Ok(BoundaryCondition::Free),
            Self::VanishingOnOccurrences {
                lineage,
                occurrences,
            } => {
                let mut cells = BTreeSet::new();
                for (vertex, cell) in &member.vertex_cells {
                    if occurrences.contains(vertex) {
                        cells.insert(*cell);
                    }
                }
                for (edge, cell) in &member.edge_cells {
                    if occurrences.contains(&edge.lower) && occurrences.contains(&edge.upper) {
                        cells.insert(*cell);
                    }
                }
                for (triple, cell) in &member.face_cells {
                    if triple.iter().all(|vertex| occurrences.contains(vertex)) {
                        cells.insert(*cell);
                    }
                }
                Ok(BoundaryCondition::VanishingOn {
                    lineage: lineage.clone(),
                    cells,
                })
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// the operator
// -------------------------------------------------------------------------------------------

/// **`Δ_k` over a declared metric and declared boundary conditions.**
///
/// Carries the active coordinate order per grade, the exact coboundaries between them and the
/// resolved metric. The coboundary entries are the complex's own oriented incidence, read through
/// the rank-one cellular sheaf of [`crate::sheaf_diffusion`], restricted to the active cells.
///
/// **This one is already closed, and not at its wire.** [`Self::validate`] re-derives `d ∘ d = 0`
/// and the adjoint characterization `W_k δ_k = d_k^T W_{k+1}` — the whole content of the operator —
/// and re-checks that the resolved metric covers the coordinate population and is positive there.
/// Every public reading calls it first, which is stronger than a wire check because it also
/// governs an operator a caller builds by hand. Moving that work into a `TryFrom` would run it
/// once at the boundary instead of at every reading and would break
/// `a_remounted_operator_with_a_poisoned_metric_refuses_rather_than_reading`, which is this
/// module's own statement of the discipline.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HodgeOperator {
    pub schema: String,
    pub lineage: String,
    pub metric: CellMetric,
    pub condition: BoundaryCondition,
    /// The top grade carrying an active cell, or `None` when the active population is empty.
    pub dimension: Option<u32>,
    coordinates: BTreeMap<u32, Vec<CausalCellId>>,
    incidence: BTreeMap<CausalCellId, BTreeMap<CausalCellId, BigInt>>,
}

impl HodgeOperator {
    /// Found the operator over a graded complex.
    pub fn found(
        lineage: impl Into<String>,
        complex: &GradedCausalComplex,
        metric: &MetricDeclaration,
        condition: &BoundaryCondition,
    ) -> Result<Self, HodgeError> {
        let active = condition.active(complex)?;
        let resolved = CellMetric::resolve(metric, complex, &active)?;

        let mut coordinates: BTreeMap<u32, Vec<CausalCellId>> = BTreeMap::new();
        for (id, body) in complex.cells() {
            if active.contains(id) {
                coordinates.entry(body.grade).or_default().push(*id);
            }
        }
        let dimension = coordinates.keys().copied().max();

        // The oriented incidence of the *active* population: the boundary coefficient of each
        // active face of each active cell, group-completed exactly as `rebase_invariants`
        // reads it. Faces outside the active population are dropped, which is precisely the
        // relative complex — the declared condition is what makes that lawful.
        let mut incidence: BTreeMap<CausalCellId, BTreeMap<CausalCellId, BigInt>> = BTreeMap::new();
        for id in &active {
            let body = complex.cell(*id)?;
            let mut faces = BTreeMap::new();
            for (face, coefficient) in body.boundary.coefficients() {
                if !active.contains(face) {
                    continue;
                }
                let value = coefficient.difference();
                if !value.is_zero() {
                    faces.insert(*face, value);
                }
            }
            incidence.insert(*id, faces);
        }

        let operator = Self {
            schema: HODGE_OPERATOR_SCHEMA.to_owned(),
            lineage: lineage.into(),
            metric: resolved,
            condition: condition.clone(),
            dimension,
            coordinates,
            incidence,
        };
        operator.validate()?;
        Ok(operator)
    }

    /// Found the operator over one member of a constraint family.
    pub fn from_member(
        member: &GradedConstraintComplex,
        metric: &MetricDeclaration,
        law: &BoundaryLaw,
    ) -> Result<Self, HodgeError> {
        let condition = law.resolve(member)?;
        Self::found(
            member.presentation_lineage.clone(),
            &member.complex,
            metric,
            &condition,
        )
    }

    /// The active cells of one grade, in the coordinate order every matrix below uses.
    pub fn cells(&self, grade: u32) -> &[CausalCellId] {
        self.coordinates
            .get(&grade)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn extent(&self, grade: u32) -> usize {
        self.cells(grade).len()
    }

    /// The active `f`-vector: how many cells of each grade the declared condition leaves.
    pub fn f_vector(&self) -> BTreeMap<u32, usize> {
        self.coordinates
            .iter()
            .map(|(grade, cells)| (*grade, cells.len()))
            .collect()
    }

    /// **The exact coboundary `d_k : C^k → C^{k+1}`.**
    ///
    /// Rows are the active `(k+1)`-cells and columns the active `k`-cells, with the entry the
    /// oriented incidence `[τ : σ]`. This is the rank-one case of
    /// [`crate::sheaf_diffusion::ExactCellularSheaf::coboundary`] restricted to the active
    /// population; [`Self::agrees_with_cellular_sheaf`] checks the two agree on a free condition.
    pub fn coboundary(&self, grade: u32) -> Result<ExactRatMatrix, HodgeError> {
        let source = self.cells(grade);
        let target = self.cells(grade.saturating_add(1));
        let column_of: BTreeMap<CausalCellId, usize> = source
            .iter()
            .enumerate()
            .map(|(at, cell)| (*cell, at))
            .collect();
        let mut rows = vec![vec![Rat::zero(); source.len()]; target.len()];
        for (row, upper) in target.iter().enumerate() {
            let Some(faces) = self.incidence.get(upper) else {
                continue;
            };
            for (face, coefficient) in faces {
                let Some(column) = column_of.get(face) else {
                    continue;
                };
                rows[row][*column] = Rat::from_integer(coefficient.clone());
            }
        }
        Ok(ExactRatMatrix::shaped(target.len(), source.len(), rows)?)
    }

    /// The declared metric of one grade as a diagonal exact matrix.
    pub fn metric_matrix(&self, grade: u32) -> Result<ExactRatMatrix, HodgeError> {
        let diagonal = self
            .cells(grade)
            .iter()
            .map(|cell| self.metric.weight(*cell).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ExactRatMatrix::from_diagonal(diagonal)?)
    }

    /// **The codifferential `δ_k = W_k^{-1} d_k^T W_{k+1} : C^{k+1} → C^k`.**
    ///
    /// Reached through [`ExactRatMatrix::metric_adjoint`], which is the owner of the statement
    /// that a bare transpose is this object only under an undeclared orthonormal chart. When
    /// either grade carries no active cell the map is the zero map of the declared shape and the
    /// `0 × 0` metric is not sent through a generic inverse.
    pub fn codifferential(&self, grade: u32) -> Result<ExactRatMatrix, HodgeError> {
        let source = self.extent(grade.saturating_add(1));
        let target = self.extent(grade);
        if source == 0 || target == 0 {
            return Ok(ExactRatMatrix::zero(target, source)?);
        }
        let coboundary = self.coboundary(grade)?;
        let domain = self.metric_matrix(grade)?;
        let codomain = self.metric_matrix(grade.saturating_add(1))?;
        Ok(coboundary.metric_adjoint(&domain, &codomain)?)
    }

    /// **`Δ_k = d_{k−1} d_{k−1}^* + d_k^* d_k`.**
    pub fn laplacian(&self, grade: u32) -> Result<ExactRatMatrix, HodgeError> {
        let extent = self.extent(grade);
        let up = {
            let coboundary = self.coboundary(grade)?;
            let codifferential = self.codifferential(grade)?;
            codifferential.multiply(&coboundary)?
        };
        let down = match grade.checked_sub(1) {
            None => ExactRatMatrix::zero(extent, extent)?,
            Some(lower) => {
                let coboundary = self.coboundary(lower)?;
                let codifferential = self.codifferential(lower)?;
                coboundary.multiply(&codifferential)?
            }
        };
        Ok(down.add(&up)?)
    }

    /// `⟪x, y⟫_k = Σ w(c) x_c y_c` in the declared metric.
    pub fn inner(&self, grade: u32, left: &[Rat], right: &[Rat]) -> Result<Rat, HodgeError> {
        let cells = self.cells(grade);
        if left.len() != cells.len() || right.len() != cells.len() {
            return Err(HodgeError::CochainWidthDisagrees {
                grade,
                expected: cells.len(),
                supplied: left.len().max(right.len()),
            });
        }
        let mut total = Rat::zero();
        for ((cell, a), b) in cells.iter().zip(left).zip(right) {
            total += self.metric.weight(*cell)? * a * b;
        }
        Ok(total)
    }

    /// **Every law this operator claims, re-derived rather than asserted.**
    ///
    /// `d_{k+1} d_k = 0` at every grade, and the adjoint characterization `W_k δ_k = d_k^T W_{k+1}`
    /// as an exact matrix identity — which is simultaneously the certificate that the metric
    /// inverse taken inside [`Self::codifferential`] is the inverse.
    pub fn validate(&self) -> Result<(), HodgeError> {
        // A remounted operator arrives through `Deserialize` with no constructor having run, so
        // the metric's positivity and its agreement with the coordinate population are re-checked
        // here rather than trusted. Every public reading calls this.
        let mut declared = BTreeSet::new();
        for cells in self.coordinates.values() {
            for cell in cells {
                if !declared.insert(*cell) {
                    return Err(HodgeError::CoordinateRepeated(*cell));
                }
                let weight = self.metric.weight(*cell)?;
                if !weight.is_positive() {
                    return Err(HodgeError::MetricWeightNotPositive {
                        lineage: self.metric.lineage.clone(),
                        cell: Some(*cell),
                        grade: None,
                    });
                }
            }
        }
        for cell in self.metric.weights.keys() {
            if !declared.contains(cell) {
                return Err(HodgeError::MetricNamesInactiveCell(*cell));
            }
        }
        for (cell, faces) in &self.incidence {
            if !declared.contains(cell) {
                return Err(HodgeError::MetricNamesInactiveCell(*cell));
            }
            for face in faces.keys() {
                if !declared.contains(face) {
                    return Err(HodgeError::MetricNamesInactiveCell(*face));
                }
            }
        }
        let Some(dimension) = self.dimension else {
            return Ok(());
        };
        for grade in 0..=dimension {
            let coboundary = self.coboundary(grade)?;
            if grade < dimension {
                let next = self.coboundary(grade + 1)?;
                let squared = next.multiply(&coboundary)?;
                if squared.entries().iter().any(|entry| !entry.is_zero()) {
                    return Err(HodgeError::CoboundarySquaredNonzero { grade });
                }
            }
            if self.extent(grade) == 0 || self.extent(grade + 1) == 0 {
                continue;
            }
            let domain = self.metric_matrix(grade)?;
            let codomain = self.metric_matrix(grade + 1)?;
            let codifferential = self.codifferential(grade)?;
            let left = domain.multiply(&codifferential)?;
            let right = coboundary.transpose()?.multiply(&codomain)?;
            if left != right {
                return Err(HodgeError::AdjointCharacterizationFails { grade });
            }
        }
        Ok(())
    }

    /// The unit-metric Laplacian of [`crate::sheaf_diffusion`] on the same complex, for the
    /// cross-check that this module's coboundary is that module's.
    ///
    /// Only meaningful under [`BoundaryCondition::Free`]: the cellular sheaf owns the whole
    /// complex, and a relative complex is this module's declaration and not that one's.
    pub fn agrees_with_cellular_sheaf(
        &self,
        complex: &GradedCausalComplex,
        grade: u32,
    ) -> Result<bool, HodgeError> {
        if self.condition != BoundaryCondition::Free {
            return Err(HodgeError::CellularSheafComparisonNeedsFreeCondition);
        }
        let sheaf = rank_one_sheaf(complex)?;
        let theirs = sheaf
            .coboundary(grade)
            .map_err(|error| HodgeError::CellularSheaf(error.to_string()))?;
        let mine = self.coboundary(grade)?;
        let theirs =
            ExactRatMatrix::shaped(theirs.rows(), theirs.columns(), theirs.entries().to_vec())?;
        Ok(theirs == mine)
    }
}

/// The rank-one cellular sheaf on a complex: one rational per cell, every restriction the identity.
///
/// This is the object whose coboundary is the ordinary cellular coboundary, and building it here
/// is how [`HodgeOperator::agrees_with_cellular_sheaf`] compares this module's incidence with
/// [`crate::sheaf_diffusion`]'s without either module reaching into the other.
fn rank_one_sheaf(
    complex: &GradedCausalComplex,
) -> Result<crate::sheaf_diffusion::ExactCellularSheaf, HodgeError> {
    use crate::sheaf_diffusion::{CellularRestriction, ExactCellularSheaf, ExactLinearMap};
    let stalks = complex.cells().keys().map(|cell| (*cell, 1_usize)).collect();
    let mut restrictions = Vec::new();
    for (upper, body) in complex.cells() {
        for lower in body.boundary.support() {
            restrictions.push(CellularRestriction {
                lower,
                upper: *upper,
                map: ExactLinearMap::identity(1),
            });
        }
    }
    ExactCellularSheaf::new(complex.clone(), stalks, restrictions)
        .map_err(|error| HodgeError::CellularSheaf(error.to_string()))
}

// -------------------------------------------------------------------------------------------
// the decomposition
// -------------------------------------------------------------------------------------------

/// **The Hodge decomposition of one cochain, exactly.**
///
/// **A remounted decomposition re-adds its own three parts.** `exact + coexact + harmonic` is
/// re-derived coordinatewise against the cochain, which is the same identity the constructor
/// checks and needs nothing the struct does not carry. The three pairings are retained as receipts
/// and are exactly zero or the decomposition is not orthogonal; whether they are the *declared
/// metric's* pairings of these three vectors is a statement about an operator this struct does not
/// carry, so that much is testimony.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "HodgeDecompositionWire")]
pub struct HodgeDecomposition {
    pub schema: String,
    pub grade: u32,
    pub cochain: Vec<Rat>,
    /// `d_{k−1} α`.
    pub exact: Vec<Rat>,
    /// `d_k^* β`.
    pub coexact: Vec<Rat>,
    /// The harmonic remainder, annihilated by `Δ_k`, by `d_k` and by `d_{k−1}^*` separately.
    pub harmonic: Vec<Rat>,
    /// One `α` with `d_{k−1} α = exact`. The fibre is `α + ker d_{k−1}`; no representative is
    /// privileged and this is a particular solution, named as one.
    pub exact_potential: Option<Vec<Rat>>,
    /// One `β` with `d_k^* β = coexact`, under the same reading.
    pub coexact_potential: Option<Vec<Rat>>,
    /// `⟪exact, coexact⟫`, `⟪exact, harmonic⟫`, `⟪coexact, harmonic⟫` — all exactly zero, retained
    /// so that a reader of the serialized value has the receipt and not the claim.
    pub pairings: [Rat; 3],
}

#[derive(Deserialize)]
struct HodgeDecompositionWire {
    schema: String,
    grade: u32,
    cochain: Vec<Rat>,
    exact: Vec<Rat>,
    coexact: Vec<Rat>,
    harmonic: Vec<Rat>,
    exact_potential: Option<Vec<Rat>>,
    coexact_potential: Option<Vec<Rat>>,
    pairings: [Rat; 3],
}

impl TryFrom<HodgeDecompositionWire> for HodgeDecomposition {
    type Error = HodgeError;

    fn try_from(wire: HodgeDecompositionWire) -> Result<Self, Self::Error> {
        let width = wire.cochain.len();
        for part in [&wire.exact, &wire.coexact, &wire.harmonic] {
            if part.len() != width {
                return Err(HodgeError::CochainWidthDisagrees {
                    grade: wire.grade,
                    expected: width,
                    supplied: part.len(),
                });
            }
        }
        for at in 0..width {
            if &wire.exact[at] + &wire.coexact[at] + &wire.harmonic[at] != wire.cochain[at] {
                return Err(HodgeError::DecompositionDoesNotSum {
                    grade: wire.grade,
                    coordinate: at,
                });
            }
        }
        for (at, pairing) in wire.pairings.iter().enumerate() {
            if !pairing.is_zero() {
                return Err(HodgeError::ComponentsNotOrthogonal {
                    grade: wire.grade,
                    pairing: at,
                });
            }
        }
        Ok(Self {
            schema: wire.schema,
            grade: wire.grade,
            cochain: wire.cochain,
            exact: wire.exact,
            coexact: wire.coexact,
            harmonic: wire.harmonic,
            exact_potential: wire.exact_potential,
            coexact_potential: wire.coexact_potential,
            pairings: wire.pairings,
        })
    }
}

/// Decompose a cochain into its exact, coexact and harmonic components.
pub fn hodge_decomposition(
    operator: &HodgeOperator,
    grade: u32,
    cochain: &[Rat],
) -> Result<HodgeDecomposition, HodgeError> {
    operator.validate()?;
    let extent = operator.extent(grade);
    if cochain.len() != extent {
        return Err(HodgeError::CochainWidthDisagrees {
            grade,
            expected: extent,
            supplied: cochain.len(),
        });
    }
    let metric = operator.metric_matrix(grade)?;

    let lower = match grade.checked_sub(1) {
        Some(lower) => operator.coboundary(lower)?,
        None => ExactRatMatrix::zero(extent, 0)?,
    };
    let codifferential = operator.codifferential(grade)?;

    let exact = project_onto_image(&lower, &metric, cochain)?;
    let coexact = project_onto_image(&codifferential, &metric, cochain)?;
    let harmonic = cochain
        .iter()
        .zip(&exact)
        .zip(&coexact)
        .map(|((value, a), b)| value - a - b)
        .collect::<Vec<_>>();

    // Re-derived, never asserted: the three sum back, the three pairings vanish, and the harmonic
    // part is in the kernel of the Laplacian *and* of both maps separately.
    for (at, value) in cochain.iter().enumerate() {
        if &exact[at] + &coexact[at] + &harmonic[at] != *value {
            return Err(HodgeError::DecompositionDoesNotSum { grade, coordinate: at });
        }
    }
    let pairings = [
        operator.inner(grade, &exact, &coexact)?,
        operator.inner(grade, &exact, &harmonic)?,
        operator.inner(grade, &coexact, &harmonic)?,
    ];
    for (at, pairing) in pairings.iter().enumerate() {
        if !pairing.is_zero() {
            return Err(HodgeError::ComponentsNotOrthogonal { grade, pairing: at });
        }
    }
    let laplacian = operator.laplacian(grade)?;
    if laplacian.apply(&harmonic)?.iter().any(|v| !v.is_zero()) {
        return Err(HodgeError::HarmonicNotAnnihilated {
            grade,
            by: "the Laplacian",
        });
    }
    let up = operator.coboundary(grade)?;
    if up.apply(&harmonic)?.iter().any(|v| !v.is_zero()) {
        return Err(HodgeError::HarmonicNotAnnihilated {
            grade,
            by: "the coboundary out of this grade",
        });
    }
    if grade > 0 {
        let down = operator.codifferential(grade - 1)?;
        if down.apply(&harmonic)?.iter().any(|v| !v.is_zero()) {
            return Err(HodgeError::HarmonicNotAnnihilated {
                grade,
                by: "the codifferential into the grade below",
            });
        }
    }

    let exact_potential = if lower.columns() == 0 {
        None
    } else {
        lower.preimage_fibre(&exact)?.map(|(particular, _)| particular)
    };
    let coexact_potential = if codifferential.columns() == 0 {
        None
    } else {
        codifferential
            .preimage_fibre(&coexact)?
            .map(|(particular, _)| particular)
    };

    Ok(HodgeDecomposition {
        schema: HODGE_DECOMPOSITION_SCHEMA.to_owned(),
        grade,
        cochain: cochain.to_vec(),
        exact,
        coexact,
        harmonic,
        exact_potential,
        coexact_potential,
        pairings,
    })
}

/// The `W`-orthogonal projection of `x` onto `image(map)`, exactly.
///
/// `B` is the exhibited image basis, `G = Bᵀ W B` its Gram matrix — invertible because the basis
/// is independent and `W` is positive definite — and the projection is `B G^{-1} Bᵀ W x`.
fn project_onto_image(
    map: &ExactRatMatrix,
    metric: &ExactRatMatrix,
    x: &[Rat],
) -> Result<Vec<Rat>, HodgeError> {
    let extent = metric.rows();
    let columns = map.image_basis()?;
    if columns.is_empty() {
        return Ok(vec![Rat::zero(); extent]);
    }
    let width = columns.len();
    let basis = ExactRatMatrix::shaped(
        extent,
        width,
        (0..extent)
            .map(|row| columns.iter().map(|column| column[row].clone()).collect())
            .collect(),
    )?;
    let transposed = basis.transpose()?;
    let gram = transposed.multiply(&metric.multiply(&basis)?)?;
    let coefficients = gram.inverse()?.apply(&transposed.apply(&metric.apply(x)?)?)?;
    Ok(basis.apply(&coefficients)?)
}

// -------------------------------------------------------------------------------------------
// the reading
// -------------------------------------------------------------------------------------------

/// **What the Hodge receiver returns at one grade.**
///
/// **A remounted reading re-derives every count it can.** The three dimensions close on the cell
/// population, the Betti number equals the harmonic dimension — the reading refuses when they
/// disagree and so does the wire — the exhibited harmonic basis is re-reduced and refused unless
/// its rank *is* the harmonic dimension it claims, the torsion coefficients are the Smith normal
/// form's own (each above one, each dividing the next), and the harmonic localization is re-read
/// against the basis beside it: its support is the coordinate support of that basis, its
/// multiplicity the basis size, and its eigenvalue exactly `0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "HodgeReadingWire")]
pub struct HodgeReading {
    pub schema: String,
    pub lineage: String,
    pub metric_lineage: String,
    pub condition_lineage: String,
    pub grade: u32,
    pub cells: usize,
    /// `rank d_{k−1}`: the dimension of the exact part.
    pub exact_dimension: usize,
    /// `rank d_k^* = rank d_k`: the dimension of the coexact part.
    pub coexact_dimension: usize,
    /// `dim ker Δ_k`.
    pub harmonic_dimension: usize,
    /// The free rank of `H_k` over `ℤ`, from the Smith normal form. Equal to
    /// [`Self::harmonic_dimension`] or the reading refuses.
    pub betti: usize,
    /// The torsion coefficients of `H_k`. **Invisible to the harmonic space**: the rational Hodge
    /// theory reads free rank only, and this is retained so that the fact is visible.
    pub torsion: Vec<BigInt>,
    /// The canonical reduced-echelon basis of `ker Δ_k`, exactly.
    pub harmonic_basis: Vec<Vec<Rat>>,
    /// Which cells carry the harmonic space, and how concentrated each basis vector is.
    pub harmonic_localization: ModeLocalization,
}

#[derive(Deserialize)]
struct HodgeReadingWire {
    schema: String,
    lineage: String,
    metric_lineage: String,
    condition_lineage: String,
    grade: u32,
    cells: usize,
    exact_dimension: usize,
    coexact_dimension: usize,
    harmonic_dimension: usize,
    betti: usize,
    torsion: Vec<BigInt>,
    harmonic_basis: Vec<Vec<Rat>>,
    harmonic_localization: ModeLocalization,
}

impl TryFrom<HodgeReadingWire> for HodgeReading {
    type Error = HodgeError;

    fn try_from(wire: HodgeReadingWire) -> Result<Self, Self::Error> {
        let grade = wire.grade;
        if wire.exact_dimension + wire.coexact_dimension + wire.harmonic_dimension != wire.cells {
            return Err(HodgeError::DimensionsDoNotClose {
                grade,
                exact: wire.exact_dimension,
                coexact: wire.coexact_dimension,
                harmonic: wire.harmonic_dimension,
                cells: wire.cells,
            });
        }
        if wire.betti != wire.harmonic_dimension {
            return Err(HodgeError::HarmonicDimensionDisagreesWithBetti {
                grade,
                harmonic: wire.harmonic_dimension,
                betti: wire.betti,
            });
        }
        if wire.harmonic_basis.len() != wire.harmonic_dimension {
            return Err(HodgeError::HodgeWireDisagrees {
                object: "reading",
                relation: "the exhibited harmonic basis against the harmonic dimension",
                declared: wire.harmonic_basis.len().to_string(),
                derived: wire.harmonic_dimension.to_string(),
            });
        }
        for vector in &wire.harmonic_basis {
            if vector.len() != wire.cells {
                return Err(HodgeError::CochainWidthDisagrees {
                    grade,
                    expected: wire.cells,
                    supplied: vector.len(),
                });
            }
        }
        // A basis is independent, and that is decided exactly by one reduction of the vectors the
        // reading already exhibits.
        if !wire.harmonic_basis.is_empty() {
            let exhibited = ExactRatMatrix::shaped(
                wire.harmonic_basis.len(),
                wire.cells,
                wire.harmonic_basis.clone(),
            )?;
            let rank = exhibited.rank()?;
            if rank != wire.harmonic_dimension {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "reading",
                    relation: "the rank of the exhibited harmonic basis against its own size",
                    declared: wire.harmonic_dimension.to_string(),
                    derived: rank.to_string(),
                });
            }
        }
        for pair in wire.torsion.windows(2) {
            if pair[0].is_zero() || !(&pair[1] % &pair[0]).is_zero() {
                return Err(HodgeError::SmithDivisibilityFails { grade });
            }
        }
        for factor in &wire.torsion {
            if *factor <= BigInt::one() {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "reading",
                    relation: "a torsion coefficient, which the Smith normal form returns above one",
                    declared: factor.to_string(),
                    derived: "above 1".to_owned(),
                });
            }
        }
        let localization = &wire.harmonic_localization;
        if localization.grade != grade
            || localization.multiplicity != wire.harmonic_dimension
            || localization.eigenvalue != EigenvalueReading::Rational(Rat::zero())
            || localization.certificate != LocalizationCertificate::ExactEigenspace
        {
            return Err(HodgeError::HodgeWireDisagrees {
                object: "reading",
                relation: "the harmonic localization, which reads the exact kernel at eigenvalue 0",
                declared: format!(
                    "grade {}, multiplicity {}, {:?}",
                    localization.grade, localization.multiplicity, localization.certificate
                ),
                derived: format!(
                    "grade {grade}, multiplicity {}, ExactEigenspace at 0",
                    wire.harmonic_dimension
                ),
            });
        }
        let carried = (0..wire.cells)
            .filter(|at| {
                wire.harmonic_basis
                    .iter()
                    .any(|vector| !vector[*at].is_zero())
            })
            .count();
        if localization.support.len() != carried {
            return Err(HodgeError::HodgeWireDisagrees {
                object: "reading",
                relation: "the harmonic support against the exhibited basis's coordinate support",
                declared: localization.support.len().to_string(),
                derived: carried.to_string(),
            });
        }
        Ok(Self {
            schema: wire.schema,
            lineage: wire.lineage,
            metric_lineage: wire.metric_lineage,
            condition_lineage: wire.condition_lineage,
            grade,
            cells: wire.cells,
            exact_dimension: wire.exact_dimension,
            coexact_dimension: wire.coexact_dimension,
            harmonic_dimension: wire.harmonic_dimension,
            betti: wire.betti,
            torsion: wire.torsion,
            harmonic_basis: wire.harmonic_basis,
            harmonic_localization: wire.harmonic_localization,
        })
    }
}

/// Read the receiver at one grade.
pub fn hodge_reading(operator: &HodgeOperator, grade: u32) -> Result<HodgeReading, HodgeError> {
    operator.validate()?;
    let cells = operator.extent(grade);
    let laplacian = operator.laplacian(grade)?;
    let harmonic_basis = laplacian.kernel_basis()?;
    let harmonic_dimension = harmonic_basis.len();

    let up = operator.coboundary(grade)?;
    let coexact_dimension = up.rank()?;
    let exact_dimension = match grade.checked_sub(1) {
        Some(lower) => operator.coboundary(lower)?.rank()?,
        None => 0,
    };
    if exact_dimension + coexact_dimension + harmonic_dimension != cells {
        return Err(HodgeError::DimensionsDoNotClose {
            grade,
            exact: exact_dimension,
            coexact: coexact_dimension,
            harmonic: harmonic_dimension,
            cells,
        });
    }

    let (betti, torsion) = betti_and_torsion(operator, grade)?;
    if betti != harmonic_dimension {
        return Err(HodgeError::HarmonicDimensionDisagreesWithBetti {
            grade,
            harmonic: harmonic_dimension,
            betti,
        });
    }

    let harmonic_localization =
        localize_exactly(operator, grade, EigenvalueReading::Rational(Rat::zero()), &harmonic_basis)?;

    Ok(HodgeReading {
        schema: HODGE_READING_SCHEMA.to_owned(),
        lineage: operator.lineage.clone(),
        metric_lineage: operator.metric.lineage.clone(),
        condition_lineage: operator.condition.lineage().to_owned(),
        grade,
        cells,
        exact_dimension,
        coexact_dimension,
        harmonic_dimension,
        betti,
        torsion,
        harmonic_basis,
        harmonic_localization,
    })
}

/// Read the receiver at every grade the active population reaches.
pub fn hodge_readings(operator: &HodgeOperator) -> Result<Vec<HodgeReading>, HodgeError> {
    let Some(dimension) = operator.dimension else {
        return Ok(Vec::new());
    };
    (0..=dimension)
        .map(|grade| hodge_reading(operator, grade))
        .collect()
}

/// The Betti number and torsion coefficients of the active complex at one grade, over `ℤ`.
///
/// Reduced by [`crate::rebase_invariants::smith_normal_form`]. The boundary matrices are
/// assembled here rather than by [`crate::rebase_invariants::boundary_matrix_on`] because that
/// owner requires a support closed under boundary, and the active population of a
/// [`BoundaryCondition::VanishingOn`] reading is the *complement* of a closed set, which is not
/// closed. The reduction itself is not reimplemented.
fn betti_and_torsion(
    operator: &HodgeOperator,
    grade: u32,
) -> Result<(usize, Vec<BigInt>), HodgeError> {
    let cells = operator.extent(grade);
    let out = smith_normal_form(&active_boundary_matrix(operator, grade), PivotRule::FirstNonzero);
    let into = smith_normal_form(
        &active_boundary_matrix(operator, grade.saturating_add(1)),
        PivotRule::SmallestMagnitude,
    );
    if !out.divisibility_holds() || !into.divisibility_holds() {
        return Err(HodgeError::SmithDivisibilityFails { grade });
    }
    let betti = cells
        .checked_sub(out.rank())
        .and_then(|value| value.checked_sub(into.rank()))
        .ok_or(HodgeError::BettiUnderflow { grade })?;
    Ok((betti, into.torsion()))
}

/// `∂_grade` restricted to the active population: rows are active `(grade−1)`-cells, columns
/// active `grade`-cells.
fn active_boundary_matrix(operator: &HodgeOperator, grade: u32) -> IntegerMatrix {
    let columns = operator.cells(grade);
    let rows: &[CausalCellId] = match grade.checked_sub(1) {
        Some(lower) => operator.cells(lower),
        None => &[],
    };
    let row_of: BTreeMap<CausalCellId, usize> = rows
        .iter()
        .enumerate()
        .map(|(at, cell)| (*cell, at))
        .collect();
    let mut matrix = IntegerMatrix::zeros(rows.len(), columns.len());
    for (column, cell) in columns.iter().enumerate() {
        let Some(faces) = operator.incidence.get(cell) else {
            continue;
        };
        for (face, coefficient) in faces {
            if let Some(row) = row_of.get(face) {
                matrix.set(*row, column, coefficient.clone());
            }
        }
    }
    matrix
}

// -------------------------------------------------------------------------------------------
// mode localization
// -------------------------------------------------------------------------------------------

/// One eigenvalue, held exactly.
///
/// **Its wire adds nothing of its own.** Every rational is a lawful rational eigenvalue reading,
/// and the isolated case is a [`crate::exact_value::AlgebraicRoot`], whose wire re-runs the Sturm
/// isolation and refuses a certificate that does not agree with the polynomial it travels with.
/// *Which* polynomial that is — this spectrum's radical rather than some other — is the relation
/// that matters, and it is enforced at [`ExactHodgeSpectrum`] where the radical is in hand.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum EigenvalueReading {
    /// Exactly this rational.
    Rational(Rat),
    /// A root of the named polynomial, isolated in a rational interval by a Sturm certificate.
    /// **Not a float and not a decimal** — the interval is the value.
    Isolated(Box<AlgebraicRoot>),
}

impl EigenvalueReading {
    /// The exact interval this reading occupies: a point interval exactly when it is rational.
    pub fn interval(&self) -> ExactInterval {
        match self {
            Self::Rational(value) => ExactInterval::point(value.clone()),
            Self::Isolated(root) => root.isolating_interval.clone(),
        }
    }

    pub fn is_rational(&self) -> bool {
        matches!(self, Self::Rational(_))
    }
}

/// **How a mode sits on the complex.**
///
/// **A remounted localization is held to which of the two statements it is making.** The
/// certificate and the eigenvalue are one choice written twice: an exact eigenspace is solved for
/// only at a rational eigenvalue and then carries one participation ratio per basis vector, and an
/// interval-blocks containment is stated only at an isolated one and then carries no participation
/// vector at all, because no eigenvector is written down. Under the containment the support is
/// re-derived as the union of the carrying blocks, and the carrying blocks cannot outnumber the
/// blocks they are drawn from. Every participation ratio is at least one, which is what
/// `(Σ w v²)² ≥ Σ w² v⁴` makes it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ModeLocalizationWire")]
pub struct ModeLocalization {
    pub schema: String,
    pub grade: u32,
    pub eigenvalue: EigenvalueReading,
    /// Geometric multiplicity for a rational eigenvalue; the multiplicity of the isolated root in
    /// the characteristic polynomial otherwise.
    pub multiplicity: usize,
    /// Where the eigenspace lives. Under [`LocalizationCertificate::ExactEigenspace`] this is
    /// exactly the set of cells at which **some** vector of the eigenspace is nonzero — a property
    /// of the subspace and not of the basis, since it is the union of the coordinate supports over
    /// any basis of it. Under [`LocalizationCertificate::IntervalBlocks`] no eigenvector is
    /// written down, so this is the union of the carrying blocks: a **containing** set, exact as
    /// a containment and not claimed to be the support itself.
    pub support: Vec<CausalCellId>,
    /// The exact rational participation ratio `(Σ w v²)² / Σ w² v⁴` of each vector of the
    /// canonical reduced-echelon kernel basis. **Basis-dependent**, and the basis is named: one
    /// for a vector on a single cell, `n` for one spread evenly over `n` equally weighted cells.
    pub participation: Vec<Rat>,
    pub certificate: LocalizationCertificate,
}

#[derive(Deserialize)]
struct ModeLocalizationWire {
    schema: String,
    grade: u32,
    eigenvalue: EigenvalueReading,
    multiplicity: usize,
    support: Vec<CausalCellId>,
    participation: Vec<Rat>,
    certificate: LocalizationCertificate,
}

impl TryFrom<ModeLocalizationWire> for ModeLocalization {
    type Error = HodgeError;

    fn try_from(wire: ModeLocalizationWire) -> Result<Self, Self::Error> {
        if wire.multiplicity == 0 {
            return Err(HodgeError::HodgeWireDisagrees {
                object: "mode localization",
                relation: "the multiplicity of a listed eigenvalue",
                declared: "0".to_owned(),
                derived: "at least 1".to_owned(),
            });
        }
        let mut seen = BTreeSet::new();
        for cell in &wire.support {
            if !seen.insert(*cell) {
                return Err(HodgeError::CoordinateRepeated(*cell));
            }
        }
        for ratio in &wire.participation {
            if *ratio < Rat::one() {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "mode localization",
                    relation: "a participation ratio, which Cauchy-Schwarz holds at or above one",
                    declared: ratio.to_string(),
                    derived: "at least 1".to_owned(),
                });
            }
        }
        match &wire.certificate {
            LocalizationCertificate::ExactEigenspace => {
                if !wire.eigenvalue.is_rational() {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "an exact eigenspace, which is solved for only at a rational eigenvalue",
                        declared: "an isolated eigenvalue".to_owned(),
                        derived: "a rational one".to_owned(),
                    });
                }
                if wire.participation.len() != wire.multiplicity {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "the participation ratios, one per exhibited basis vector",
                        declared: wire.participation.len().to_string(),
                        derived: wire.multiplicity.to_string(),
                    });
                }
            }
            LocalizationCertificate::IntervalBlocks { carrying, blocks } => {
                if wire.eigenvalue.is_rational() {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "an interval-blocks containment, stated only at an isolated eigenvalue",
                        declared: "a rational eigenvalue".to_owned(),
                        derived: "an isolated one".to_owned(),
                    });
                }
                if !wire.participation.is_empty() {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "the participation ratios, which name no eigenvector under a containment",
                        declared: wire.participation.len().to_string(),
                        derived: "0".to_owned(),
                    });
                }
                if carrying.is_empty() || carrying.len() > *blocks {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "the carrying blocks against the block population they come from",
                        declared: carrying.len().to_string(),
                        derived: format!("between 1 and {blocks}"),
                    });
                }
                let union: Vec<CausalCellId> = carrying.iter().flatten().copied().collect();
                if union != wire.support {
                    return Err(HodgeError::HodgeWireDisagrees {
                        object: "mode localization",
                        relation: "the support against the union of the carrying blocks",
                        declared: wire.support.len().to_string(),
                        derived: union.len().to_string(),
                    });
                }
            }
        }
        Ok(Self {
            schema: wire.schema,
            grade: wire.grade,
            eigenvalue: wire.eigenvalue,
            multiplicity: wire.multiplicity,
            support: wire.support,
            participation: wire.participation,
            certificate: wire.certificate,
        })
    }
}

/// What kind of statement the localization is.
///
/// **Every relation it has is with the localization it sits in, so it is closed there.** That the
/// carrying blocks are non-empty and no more numerous than the blocks they are drawn from, that
/// their union is the support, that a containment carries no participation vector and that an
/// exact eigenspace stands only at a rational eigenvalue are all statements needing the fields
/// beside this one; [`ModeLocalization`]'s wire enforces each of them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LocalizationCertificate {
    /// The eigenvalue is rational, so the eigenspace was solved for exactly and the support and
    /// participation are the eigenspace's own.
    ExactEigenspace,
    /// The eigenvalue is irrational. The statement is that every eigenvector is supported inside
    /// the named decoupled blocks of `Δ_k`, certified by the sign of each block's squarefree
    /// characteristic factor at the two rational endpoints of the isolating interval. The
    /// participation vector is empty: no eigenvector is written down.
    IntervalBlocks {
        /// The blocks whose characteristic polynomial vanishes at this eigenvalue.
        carrying: Vec<Vec<CausalCellId>>,
        /// How many decoupled blocks `Δ_k` has in total.
        blocks: usize,
    },
}

fn localize_exactly(
    operator: &HodgeOperator,
    grade: u32,
    eigenvalue: EigenvalueReading,
    basis: &[Vec<Rat>],
) -> Result<ModeLocalization, HodgeError> {
    let cells = operator.cells(grade);
    for vector in basis {
        if vector.len() != cells.len() {
            return Err(HodgeError::CochainWidthDisagrees {
                grade,
                expected: cells.len(),
                supplied: vector.len(),
            });
        }
    }
    let mut support = Vec::new();
    for (at, cell) in cells.iter().enumerate() {
        if basis.iter().any(|vector| !vector[at].is_zero()) {
            support.push(*cell);
        }
    }
    let mut participation = Vec::with_capacity(basis.len());
    for vector in basis {
        let mut mass = Rat::zero();
        let mut fourth = Rat::zero();
        for (at, cell) in cells.iter().enumerate() {
            let weight = operator.metric.weight(*cell)?;
            let square = &vector[at] * &vector[at];
            let term = weight * &square;
            mass += &term;
            fourth += &term * &term;
        }
        if fourth.is_zero() {
            return Err(HodgeError::ParticipationOfZeroMode { grade });
        }
        participation.push(&mass * &mass / fourth);
    }
    Ok(ModeLocalization {
        schema: MODE_LOCALIZATION_SCHEMA.to_owned(),
        grade,
        eigenvalue,
        multiplicity: basis.len(),
        support,
        participation,
        certificate: LocalizationCertificate::ExactEigenspace,
    })
}

// -------------------------------------------------------------------------------------------
// the spectrum
// -------------------------------------------------------------------------------------------

/// **The spectrum of `Δ_k`, held exactly.**
///
/// **A remounted spectrum re-derives almost all of itself from its own characteristic polynomial.**
/// This is the one object here that genuinely travels — `refine_spectral_gap` reads its `radical`
/// and bisects against it, [`HodgeFamily`] compares two of them — so it is closed the hardest:
///
/// - `∏ V_i^i` is re-multiplied and refused unless it is the characteristic polynomial, which pins
///   the whole squarefree decomposition;
/// - `radical` is re-derived as `(∏ V_i).primitive_integer_form()`, so the polynomial every later
///   Sturm count is taken against is this spectrum's own and not a substituted one;
/// - `trace` is `−c_{n−1}` of a monic `det(sI − Δ_k)`, which is an exact identity and not a
///   restatement;
/// - every rational eigenvalue is evaluated on the characteristic polynomial and its multiplicity
///   re-read off the squarefree decomposition, and every isolated one must carry *this* radical as
///   its polynomial — its own wire has already re-run the Sturm isolation — with its multiplicity
///   re-read the same way;
/// - the multiplicities sum to the extent, the eigenvalue intervals are ascending and pairwise
///   non-overlapping, `kernel_multiplicity` is the multiplicity carried at `0`, and the
///   localization is one per distinct eigenvalue in that same ascending order;
/// - `spectral_gap` is absent exactly when nothing but `0` is in the spectrum and otherwise lies
///   inside the least non-zero eigenvalue's interval with a strictly positive lower bound.
///
/// What remains testimony is that this characteristic polynomial is `Δ_k`'s: the operator is not
/// carried, and a spectrum remounted alone is testimony about it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ExactHodgeSpectrumWire")]
pub struct ExactHodgeSpectrum {
    pub schema: String,
    pub grade: u32,
    pub extent: usize,
    /// `tr Δ_k`. Positive semidefiniteness makes this an exact upper bound on every eigenvalue,
    /// which is what bounds the isolation.
    pub trace: Rat,
    pub characteristic: RationalPolynomial,
    /// The primitive integer form of the squarefree part. Retained because it is the polynomial
    /// every Sturm count below is taken against, so a later reader — or
    /// [`refine_spectral_gap`] — can narrow an isolating interval without recomputing it.
    pub radical: IntegerPolynomial,
    /// The squarefree decomposition keyed by multiplicity: `char = ∏ V_i^i`.
    pub squarefree: BTreeMap<u32, RationalPolynomial>,
    /// Every rational eigenvalue with its multiplicity in the characteristic polynomial, ascending.
    /// Complete, not a sample.
    pub rational_eigenvalues: Vec<(Rat, usize)>,
    /// Every irrational eigenvalue, each as a polynomial plus an isolating rational interval plus
    /// its Sturm certificate, with its multiplicity. Ascending.
    pub isolated_eigenvalues: Vec<(AlgebraicRoot, usize)>,
    /// The multiplicity of `0`, which is `dim ker Δ_k` because `Δ_k` is self-adjoint in the
    /// declared inner product and therefore diagonalizable.
    pub kernel_multiplicity: usize,
    /// **The spectral gap: the smallest positive eigenvalue, as an exact interval.** A point
    /// interval exactly when that eigenvalue is rational. `None` when `Δ_k = 0`.
    pub spectral_gap: Option<ExactInterval>,
    /// One localization per distinct eigenvalue, ascending.
    pub localization: Vec<ModeLocalization>,
    /// How deep the bisection actually descended, against the bound it was given.
    pub isolation_depth: u32,
}

#[derive(Deserialize)]
struct ExactHodgeSpectrumWire {
    schema: String,
    grade: u32,
    extent: usize,
    trace: Rat,
    characteristic: RationalPolynomial,
    radical: IntegerPolynomial,
    squarefree: BTreeMap<u32, RationalPolynomial>,
    rational_eigenvalues: Vec<(Rat, usize)>,
    isolated_eigenvalues: Vec<(AlgebraicRoot, usize)>,
    kernel_multiplicity: usize,
    spectral_gap: Option<ExactInterval>,
    localization: Vec<ModeLocalization>,
    isolation_depth: u32,
}

impl TryFrom<ExactHodgeSpectrumWire> for ExactHodgeSpectrum {
    type Error = HodgeError;

    fn try_from(wire: ExactHodgeSpectrumWire) -> Result<Self, Self::Error> {
        let grade = wire.grade;
        if wire.extent == 0 {
            return Err(HodgeError::NothingToDiagonalize { grade });
        }
        if wire.characteristic.degree() != Some(wire.extent) || !wire.characteristic.is_monic() {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the characteristic polynomial as a monic of the declared extent",
                declared: format!(
                    "degree {:?}, monic {}",
                    wire.characteristic.degree(),
                    wire.characteristic.is_monic()
                ),
                derived: format!("monic of degree {}", wire.extent),
            });
        }
        // `det(sI − Δ) = s^n − (tr Δ) s^{n−1} + …`, so the trace is a coefficient and not a
        // separate claim.
        let derived_trace = -wire.characteristic.coefficient(wire.extent - 1);
        if derived_trace != wire.trace {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the trace against the characteristic polynomial's own subleading coefficient",
                declared: wire.trace.to_string(),
                derived: derived_trace.to_string(),
            });
        }
        // `char = ∏ V_i^i`, re-multiplied exactly; and the radical is the primitive integer form of
        // `∏ V_i`, which the same product gives for free.
        let mut product = RationalPolynomial::one();
        let mut squarefree_part = RationalPolynomial::one();
        for (multiplicity, factor) in &wire.squarefree {
            // The multiplicity sizes the re-multiplication, so it is bounded against the extent it
            // has to account for **before** anything is formed from it: `i · deg V_i ≤ n` with
            // `deg V_i ≥ 1` gives `i ≤ n`, and a hostile `u32` is refused here rather than run.
            if *multiplicity == 0
                || *multiplicity as usize > wire.extent
                || factor.degree().is_none_or(|degree| degree == 0)
            {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "a squarefree factor, nonconstant at a multiplicity the extent can hold",
                    declared: format!("multiplicity {multiplicity}, degree {:?}", factor.degree()),
                    derived: format!("a degree above zero at a multiplicity in 1..={}", wire.extent),
                });
            }
            // Squarefreeness is established here, once per factor, so that every multiplicity read
            // below costs two exact evaluations rather than a fresh gcd.
            if !factor.is_monic() || factor.squarefree_part()? != *factor {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "a factor of the decomposition, which is monic and squarefree",
                    declared: format!("{:?}", factor.coefficients()),
                    derived: format!("{:?}", factor.squarefree_part()?.coefficients()),
                });
            }
            squarefree_part = squarefree_part.times(factor);
            for _ in 0..*multiplicity {
                product = product.times(factor);
            }
        }
        if product != wire.characteristic {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the squarefree decomposition re-multiplied against the characteristic polynomial",
                declared: format!("{:?}", wire.characteristic.coefficients()),
                derived: format!("{:?}", product.coefficients()),
            });
        }
        let derived_radical = squarefree_part.primitive_integer_form()?;
        if derived_radical != wire.radical {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the radical against the primitive integer form of the squarefree part",
                declared: format!("{:?}", wire.radical.coefficients),
                derived: format!("{:?}", derived_radical.coefficients),
            });
        }

        let mut accounted = 0_usize;
        for pair in wire.rational_eigenvalues.windows(2) {
            if pair[0].0 >= pair[1].0 {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "the rational eigenvalues, ascending with each one listed once",
                    declared: format!("{} then {}", pair[0].0, pair[1].0),
                    derived: "strictly ascending".to_owned(),
                });
            }
        }
        for (value, multiplicity) in &wire.rational_eigenvalues {
            if value.is_negative() {
                return Err(HodgeError::SpectrumNotPositiveSemidefinite { grade });
            }
            if !wire.characteristic.evaluate(value).is_zero() {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "a declared rational eigenvalue evaluated on the characteristic polynomial",
                    declared: value.to_string(),
                    derived: wire.characteristic.evaluate(value).to_string(),
                });
            }
            let derived = multiplicity_in(&wire.squarefree, value)?;
            if derived != *multiplicity {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "a rational eigenvalue's multiplicity against the squarefree decomposition",
                    declared: multiplicity.to_string(),
                    derived: derived.to_string(),
                });
            }
            accounted += multiplicity;
        }
        for pair in wire.isolated_eigenvalues.windows(2) {
            if pair[0].0.isolating_interval.lower >= pair[1].0.isolating_interval.lower {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "the isolated eigenvalues, listed ascending",
                    declared: format!(
                        "{} then {}",
                        pair[0].0.isolating_interval.lower, pair[1].0.isolating_interval.lower
                    ),
                    derived: "strictly ascending".to_owned(),
                });
            }
        }
        for (root, multiplicity) in &wire.isolated_eigenvalues {
            if root.polynomial != wire.radical {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "an isolated eigenvalue's polynomial against this spectrum's radical",
                    declared: format!("{:?}", root.polynomial.coefficients),
                    derived: format!("{:?}", wire.radical.coefficients),
                });
            }
            let derived =
                multiplicity_of_isolated_squarefree(&wire.squarefree, &root.isolating_interval)?;
            if derived != *multiplicity {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "an isolated eigenvalue's multiplicity against the squarefree decomposition",
                    declared: multiplicity.to_string(),
                    derived: derived.to_string(),
                });
            }
            accounted += multiplicity;
        }
        if accounted != wire.extent {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the eigenvalue multiplicities summed against the extent they account for",
                declared: accounted.to_string(),
                derived: wire.extent.to_string(),
            });
        }
        let kernel = wire
            .rational_eigenvalues
            .iter()
            .find(|(value, _)| value.is_zero())
            .map_or(0, |(_, multiplicity)| *multiplicity);
        if kernel != wire.kernel_multiplicity {
            return Err(HodgeError::KernelMultiplicityDisagrees {
                grade,
                algebraic: wire.kernel_multiplicity,
                geometric: kernel,
            });
        }

        // The ascending order the constructor emits, re-derived from the two populations.
        let mut ordered: Vec<(ExactInterval, EigenvalueReading)> = wire
            .rational_eigenvalues
            .iter()
            .map(|(value, _)| {
                (
                    ExactInterval::point(value.clone()),
                    EigenvalueReading::Rational(value.clone()),
                )
            })
            .chain(wire.isolated_eigenvalues.iter().map(|(root, _)| {
                (
                    root.isolating_interval.clone(),
                    EigenvalueReading::Isolated(Box::new(root.clone())),
                )
            }))
            .collect();
        ordered.sort_by(|left, right| {
            left.0
                .lower
                .cmp(&right.0.lower)
                .then(left.0.upper.cmp(&right.0.upper))
        });
        for pair in ordered.windows(2) {
            if pair[0].0.upper > pair[1].0.lower {
                return Err(HodgeError::SpectrumIntervalsOverlap { grade });
            }
        }
        if wire.localization.len() != ordered.len() {
            return Err(HodgeError::SpectrumWireDisagrees {
                relation: "the localization count against the distinct eigenvalue population",
                declared: wire.localization.len().to_string(),
                derived: ordered.len().to_string(),
            });
        }
        for (mode, (_, eigenvalue)) in wire.localization.iter().zip(&ordered) {
            if mode.grade != grade || mode.eigenvalue != *eigenvalue {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "a localization against the eigenvalue it stands at, in ascending order",
                    declared: format!("grade {}, {:?}", mode.grade, mode.eigenvalue.interval()),
                    derived: format!("grade {grade}, {:?}", eigenvalue.interval()),
                });
            }
        }

        let least_positive = ordered
            .iter()
            .find(|(_, eigenvalue)| {
                !matches!(eigenvalue, EigenvalueReading::Rational(value) if value.is_zero())
            });
        match (&wire.spectral_gap, least_positive) {
            (None, None) => {}
            (Some(gap), Some((interval, eigenvalue))) => {
                if !gap.lower.is_positive() {
                    return Err(HodgeError::SpectralGapNotSeparated { grade });
                }
                let held = match eigenvalue {
                    EigenvalueReading::Rational(value) => *gap == ExactInterval::point(value.clone()),
                    EigenvalueReading::Isolated(_) => {
                        gap.lower >= interval.lower && gap.upper <= interval.upper
                    }
                };
                if !held {
                    return Err(HodgeError::SpectrumWireDisagrees {
                        relation: "the spectral gap against the least non-zero eigenvalue's own interval",
                        declared: format!("[{}, {}]", gap.lower, gap.upper),
                        derived: format!("inside [{}, {}]", interval.lower, interval.upper),
                    });
                }
            }
            _ => {
                return Err(HodgeError::SpectrumWireDisagrees {
                    relation: "the spectral gap, absent exactly when nothing but zero is in the spectrum",
                    declared: format!("present {}", wire.spectral_gap.is_some()),
                    derived: format!("present {}", least_positive.is_some()),
                });
            }
        }
        if wire.isolation_depth > ISOLATION_DEPTH_CEILING {
            return Err(HodgeError::IsolationDepthBoundTooLarge {
                bound: wire.isolation_depth,
                ceiling: ISOLATION_DEPTH_CEILING,
            });
        }
        Ok(Self {
            schema: wire.schema,
            grade,
            extent: wire.extent,
            trace: wire.trace,
            characteristic: wire.characteristic,
            radical: wire.radical,
            squarefree: wire.squarefree,
            rational_eigenvalues: wire.rational_eigenvalues,
            isolated_eigenvalues: wire.isolated_eigenvalues,
            kernel_multiplicity: wire.kernel_multiplicity,
            spectral_gap: wire.spectral_gap,
            localization: wire.localization,
            isolation_depth: wire.isolation_depth,
        })
    }
}

impl ExactHodgeSpectrum {
    /// The number of distinct eigenvalues.
    pub fn distinct(&self) -> usize {
        self.rational_eigenvalues.len() + self.isolated_eigenvalues.len()
    }

    /// Whether every direction is accounted for by a rational eigenvalue.
    pub fn is_completely_rational(&self) -> bool {
        self.isolated_eigenvalues.is_empty()
    }

    /// The eigenvalue intervals, ascending and pairwise non-overlapping.
    pub fn intervals(&self) -> Vec<ExactInterval> {
        self.localization
            .iter()
            .map(|mode| mode.eigenvalue.interval())
            .collect()
    }
}

/// The default bisection depth. Each step halves the interval, so this is `2^-64` of the trace
/// bound before the isolation refuses — far beyond what any separation here needs, and an explicit
/// refusal rather than a loop.
pub const DEFAULT_ISOLATION_DEPTH: u32 = 64;

/// **The ceiling on a declared isolation depth.**
///
/// [definition] `depth_bound` is a caller's declaration and it sizes the descent, so it needs a
/// ceiling of its own. Each bisection halves the interval, so this ceiling narrows the trace
/// bound by a factor of `2^-1024` — beyond any separation an exact rational spectrum of the size
/// this receiver diagonalizes can present — and it simultaneously bounds the isolation worklist,
/// which never holds more than `depth_bound + 1` pending intervals. A larger declaration is
/// refused by name with [`HodgeError::IsolationDepthBoundTooLarge`] rather than accepted and
/// discovered at the machine's expense.
pub const ISOLATION_DEPTH_CEILING: u32 = 1024;

/// **Read the exact spectrum of `Δ_k`.**
pub fn exact_hodge_spectrum(
    operator: &HodgeOperator,
    grade: u32,
    depth_bound: u32,
) -> Result<ExactHodgeSpectrum, HodgeError> {
    if depth_bound > ISOLATION_DEPTH_CEILING {
        return Err(HodgeError::IsolationDepthBoundTooLarge {
            bound: depth_bound,
            ceiling: ISOLATION_DEPTH_CEILING,
        });
    }
    operator.validate()?;
    let laplacian = operator.laplacian(grade)?;
    let extent = laplacian.rows();
    if extent == 0 {
        return Err(HodgeError::NothingToDiagonalize { grade });
    }
    let mut trace = Rat::zero();
    for at in 0..extent {
        trace += laplacian.get(at, at)?.clone();
    }

    let characteristic = characteristic_polynomial(&laplacian)?;
    let squarefree = characteristic.squarefree_decomposition()?;
    let radical = characteristic.squarefree_part()?;
    let distinct = radical.degree().unwrap_or(0);

    // Every rational root, completely, by the lifting route. `lattice_gauge::exact_spectrum`'s
    // census answers the same question from the Cauchy bound of the monic companion; on a
    // Laplacian that bound is set by coefficients of Hadamard size and the descent is the cost
    // its own module head measured.
    let mut rational_roots = rational_roots_by_lifting(&radical)?;
    rational_roots.sort();
    let rational_set: BTreeSet<Rat> = rational_roots.iter().cloned().collect();

    // Positive semidefinite in the declared metric, so the whole spectrum sits in `[0, tr]`.
    let one = Rat::one();
    let lower = -one.clone();
    let upper = &trace + &one;
    let primitive = radical.primitive_integer_form()?;

    // **One chain for the whole reading.** Every count below — the isolation's bisections, the
    // certificates, the gap refinement — is taken against this one `SturmChain`, which is the
    // difference between this reading and the one that rebuilt a rational remainder sequence per
    // count. See `exact_value::SturmChain`.
    let chain = primitive.sturm_chain()?;

    let mut isolated = Vec::new();
    let mut depth_reached = 0_u32;
    if primitive.degree() > 0 {
        let enclosure = ExactInterval::new(lower.clone(), upper.clone())?;
        let (intervals, reached) =
            isolate_against_chain(&primitive, &chain, &enclosure, depth_bound)
                .map_err(isolation_refusal)?;
        isolated = intervals;
        depth_reached = reached;
    }
    if isolated.len() != distinct {
        return Err(HodgeError::SpectrumIncomplete {
            grade,
            isolated: isolated.len(),
            distinct,
        });
    }

    // Each isolating interval holds exactly one root of the radical. The rational population is
    // known exactly, so an interval holding one of them is that eigenvalue and every other
    // interval holds an irrational one.
    let mut rational_eigenvalues: Vec<(Rat, usize)> = Vec::new();
    let mut isolated_eigenvalues: Vec<(AlgebraicRoot, usize)> = Vec::new();
    let mut ordered: Vec<(ExactInterval, EigenvalueReading)> = Vec::new();
    for interval in &isolated {
        let inside: Vec<&Rat> = rational_set
            .iter()
            .filter(|value| interval.lower < **value && **value < interval.upper)
            .collect();
        if inside.len() > 1 {
            return Err(HodgeError::IsolationHoldsTwoRoots { grade });
        }
        match inside.first() {
            Some(value) => {
                let multiplicity = multiplicity_in(&squarefree, value)?;
                rational_eigenvalues.push(((*value).clone(), multiplicity));
                ordered.push((
                    ExactInterval::point((*value).clone()),
                    EigenvalueReading::Rational((*value).clone()),
                ));
            }
            None => {
                let root =
                    AlgebraicRoot::isolate_against(primitive.clone(), interval.clone(), &chain)?;
                let multiplicity = multiplicity_of_isolated(&squarefree, interval)?;
                isolated_eigenvalues.push((root.clone(), multiplicity));
                ordered.push((
                    interval.clone(),
                    EigenvalueReading::Isolated(Box::new(root)),
                ));
            }
        }
    }
    ordered.sort_by(|left, right| {
        left.0
            .lower
            .cmp(&right.0.lower)
            .then(left.0.upper.cmp(&right.0.upper))
    });
    for pair in ordered.windows(2) {
        if pair[0].0.upper > pair[1].0.lower {
            return Err(HodgeError::SpectrumIntervalsOverlap { grade });
        }
    }

    let kernel_multiplicity = rational_eigenvalues
        .iter()
        .find(|(value, _)| value.is_zero())
        .map(|(_, multiplicity)| *multiplicity)
        .unwrap_or(0);
    let measured_kernel = laplacian.kernel_basis()?.len();
    if kernel_multiplicity != measured_kernel {
        return Err(HodgeError::KernelMultiplicityDisagrees {
            grade,
            algebraic: kernel_multiplicity,
            geometric: measured_kernel,
        });
    }

    for (value, _) in &rational_eigenvalues {
        if value.is_negative() {
            return Err(HodgeError::SpectrumNotPositiveSemidefinite { grade });
        }
    }

    // **The gap is the smallest eigenvalue that is not zero**, and it is returned as an interval
    // whose lower bound is exactly positive. A rational eigenvalue is its own point interval; an
    // irrational one is bisected away from zero until its certificate is strictly positive.
    let mut spectral_gap = None;
    for (interval, eigenvalue) in &ordered {
        if matches!(eigenvalue, EigenvalueReading::Rational(value) if value.is_zero()) {
            continue;
        }
        spectral_gap = Some(match eigenvalue {
            EigenvalueReading::Rational(value) => ExactInterval::point(value.clone()),
            EigenvalueReading::Isolated(_) => {
                refine_above_zero(&chain, interval, depth_bound, grade)?
            }
        });
        break;
    }

    let blocks = decoupled_blocks(&laplacian)?;
    let block_characteristics = blocks
        .iter()
        .map(|block| block_characteristic(&laplacian, block))
        .collect::<Result<Vec<_>, _>>()?;
    let mut product = RationalPolynomial::one();
    for factor in &block_characteristics {
        product = product.times(factor);
    }
    if product != characteristic {
        return Err(HodgeError::BlockProductDisagrees { grade });
    }

    let cells = operator.cells(grade);
    let mut localization = Vec::with_capacity(ordered.len());
    for (interval, eigenvalue) in &ordered {
        match eigenvalue {
            EigenvalueReading::Rational(value) => {
                let shifted = laplacian.subtract(&ExactRatMatrix::identity(extent)?.scaled(value))?;
                let basis = shifted.kernel_basis()?;
                localization.push(localize_exactly(
                    operator,
                    grade,
                    eigenvalue.clone(),
                    &basis,
                )?);
            }
            EigenvalueReading::Isolated(root) => {
                let mut carrying = Vec::new();
                for (block, factor) in blocks.iter().zip(&block_characteristics) {
                    if carries_root(factor, interval)? {
                        carrying.push(block.iter().map(|at| cells[*at]).collect::<Vec<_>>());
                    }
                }
                if carrying.is_empty() {
                    return Err(HodgeError::NoBlockCarriesEigenvalue { grade });
                }
                let support = carrying.iter().flatten().copied().collect::<Vec<_>>();
                localization.push(ModeLocalization {
                    schema: MODE_LOCALIZATION_SCHEMA.to_owned(),
                    grade,
                    eigenvalue: EigenvalueReading::Isolated(root.clone()),
                    multiplicity: multiplicity_of_isolated(&squarefree, interval)?,
                    support,
                    participation: Vec::new(),
                    certificate: LocalizationCertificate::IntervalBlocks {
                        carrying: carrying.clone(),
                        blocks: blocks.len(),
                    },
                });
            }
        }
    }

    Ok(ExactHodgeSpectrum {
        schema: HODGE_SPECTRUM_SCHEMA.to_owned(),
        grade,
        extent,
        trace,
        characteristic,
        radical: primitive,
        squarefree,
        rational_eigenvalues,
        isolated_eigenvalues,
        kernel_multiplicity,
        spectral_gap,
        localization,
        isolation_depth: depth_reached,
    })
}

/// **Narrow the spectral gap's isolating interval below a declared width.**
///
/// [definition] An isolating interval is a *certificate* that one root lies inside it, and its
/// width is whatever the isolation happened to need. Comparing two operators' gaps needs the
/// certificates to be narrow enough to be disjoint, and that is a separate, declared request: the
/// caller names the width it wants and this bisects to it, refusing above its depth bound rather
/// than descending without one. A rational gap is already a point and is returned unchanged.
///
/// Every endpoint stays off the exactly known rational root population, so the Sturm count that
/// decides each halving is always lawful.
pub fn refine_spectral_gap(
    spectrum: &ExactHodgeSpectrum,
    width: &Rat,
    depth_bound: u32,
) -> Result<ExactInterval, HodgeError> {
    if !width.is_positive() {
        return Err(HodgeError::RefinementWidthNotPositive);
    }
    let Some(interval) = spectrum.spectral_gap.clone() else {
        return Err(HodgeError::NoPositiveEigenvalue {
            grade: spectrum.grade,
        });
    };
    if interval.is_point() {
        return Ok(interval);
    }
    // One chain for the whole refinement, not one per halving.
    let chain = spectrum.radical.sturm_chain()?;
    let two = Rat::from_integer(BigInt::from(2));
    let mut lower = interval.lower;
    let mut upper = interval.upper;
    let mut steps = 0_u32;
    while &upper - &lower > *width {
        if steps >= depth_bound {
            return Err(HodgeError::IsolationDepthExceeded { bound: depth_bound });
        }
        steps += 1;
        let mut middle = (&lower + &upper) / &two;
        let mut attempts = 0_usize;
        while chain.vanishes_at(&middle) {
            middle = (&lower + &middle) / &two;
            attempts += 1;
            if attempts > chain.len() + 2 {
                return Err(HodgeError::IsolationSplitUnavailable);
            }
        }
        let below = ExactInterval::new(lower.clone(), middle.clone())?;
        if chain.distinct_root_count(&below)? == 1 {
            upper = middle;
        } else {
            lower = middle;
        }
    }
    Ok(ExactInterval::new(lower, upper)?)
}

/// The multiplicity of a rational value in the squarefree decomposition.
///
/// A value that is a root of the characteristic polynomial is a root of exactly one `V_i`, so an
/// absent multiplicity is a broken decomposition and not a zero: it is returned as
/// [`HodgeError::MultiplicityNotFound`], the same refusal [`multiplicity_of_isolated`] makes.
fn multiplicity_in(
    squarefree: &BTreeMap<u32, RationalPolynomial>,
    value: &Rat,
) -> Result<usize, HodgeError> {
    squarefree
        .iter()
        .find(|(_, factor)| factor.evaluate(value).is_zero())
        .map(|(multiplicity, _)| *multiplicity as usize)
        .ok_or(HodgeError::MultiplicityNotFound)
}

/// The multiplicity of the one root an interval isolates, read off the squarefree decomposition.
///
/// Each `V_i` is squarefree and the interval holds one root of the radical, so `V_i` has at most
/// one, simple, root there and a sign change across the endpoints is that root. The endpoints are
/// never roots of the radical, hence never roots of any `V_i`.
fn multiplicity_of_isolated(
    squarefree: &BTreeMap<u32, RationalPolynomial>,
    interval: &ExactInterval,
) -> Result<usize, HodgeError> {
    for (multiplicity, factor) in squarefree {
        if carries_root(factor, interval)? {
            return Ok(*multiplicity as usize);
        }
    }
    Err(HodgeError::MultiplicityNotFound)
}

/// [`multiplicity_of_isolated`] for a decomposition whose factors are **already known squarefree**.
///
/// [`carries_root`] re-extracts a squarefree part at every call, because it serves callers holding
/// a factor nothing has checked — a block characteristic polynomial, for instance. A remounted
/// spectrum establishes squarefreeness once per factor while it is re-multiplying the
/// decomposition, so every isolated eigenvalue after that costs two exact evaluations rather than a
/// fresh gcd at the full degree. On the measured M5 24-cell Laplacian, with twenty-two isolated
/// eigenvalues against one or two factors, that is the difference between forty gcds and two.
fn multiplicity_of_isolated_squarefree(
    squarefree: &BTreeMap<u32, RationalPolynomial>,
    interval: &ExactInterval,
) -> Result<usize, HodgeError> {
    for (multiplicity, factor) in squarefree {
        let low = factor.evaluate(&interval.lower);
        let high = factor.evaluate(&interval.upper);
        if low.is_zero() || high.is_zero() {
            return Err(HodgeError::IsolationEndpointIsARoot);
        }
        if low.is_negative() != high.is_negative() {
            return Ok(*multiplicity as usize);
        }
    }
    Err(HodgeError::MultiplicityNotFound)
}

/// Whether a polynomial whose roots in this interval are simple has a root in it, decided by the
/// signs of its squarefree part at the two endpoints.
fn carries_root(
    polynomial: &RationalPolynomial,
    interval: &ExactInterval,
) -> Result<bool, HodgeError> {
    if polynomial.degree().unwrap_or(0) == 0 {
        return Ok(false);
    }
    let radical = polynomial.squarefree_part()?;
    let low = radical.evaluate(&interval.lower);
    let high = radical.evaluate(&interval.upper);
    if low.is_zero() || high.is_zero() {
        return Err(HodgeError::IsolationEndpointIsARoot);
    }
    Ok(low.is_negative() != high.is_negative())
}

/// The owner's isolation refusals, in this module's own species.
///
/// [definition] The descent moved to `rational_polynomial`; its refusals are the same three this
/// module always named, so they are mapped back rather than surfaced as a foreign error. A caller
/// matching [`HodgeError::IsolationDepthExceeded`] sees what it always saw.
fn isolation_refusal(error: ExactPolynomialError) -> HodgeError {
    match error {
        ExactPolynomialError::IsolationDepthExceeded { bound } => {
            HodgeError::IsolationDepthExceeded { bound }
        }
        ExactPolynomialError::IsolationDepthBoundTooLarge { bound, ceiling } => {
            HodgeError::IsolationDepthBoundTooLarge { bound, ceiling }
        }
        ExactPolynomialError::NoInteriorNonRoot => HodgeError::IsolationSplitUnavailable,
        other => HodgeError::Polynomial(other),
    }
}

/// **The isolation is `rational_polynomial::isolate_against_chain`'s, not this module's.**
///
/// [definition] This module used to carry its own worklist bisection, because the census owner's
/// descent ran from a Cauchy bound that is astronomically wider than a Laplacian's spectrum. That
/// bound is now a certified `k`-th root bound with the two sides counted separately
/// (`rational_polynomial::RealRootEnclosure`) and the descent takes a declared enclosure as a
/// first-class argument, so this module supplies `[−1, tr Δ_k + 1]` — the bound positive
/// semidefiniteness gives it — and the owner does the descent. The split rule, the pigeonhole
/// termination, the worklist and the ascending order are the same ones this module had; there is
/// simply one copy of them now.
/// Bisect an isolating interval until its lower bound is exactly positive.
///
/// `Δ_k` is positive semidefinite, so a root that is not zero is strictly positive and this
/// terminates; the bound is a declared ceiling on the descent and not a tolerance. The refined
/// endpoints are never roots, so the interval is still a lawful Sturm certificate.
fn refine_above_zero(
    chain: &SturmChain,
    interval: &ExactInterval,
    bound: u32,
    grade: u32,
) -> Result<ExactInterval, HodgeError> {
    let mut lower = interval.lower.clone();
    let mut upper = interval.upper.clone();
    let two = Rat::from_integer(BigInt::from(2));
    let mut steps = 0_u32;
    while !lower.is_positive() {
        if steps >= bound {
            return Err(HodgeError::IsolationDepthExceeded { bound });
        }
        steps += 1;
        if !upper.is_positive() {
            return Err(HodgeError::SpectrumNotPositiveSemidefinite { grade });
        }
        if lower.is_negative() {
            // Zero is not a root here: if it were, it would be a rational eigenvalue carrying its
            // own point interval, and the disjointness check above would already have refused.
            if chain.vanishes_at(&Rat::zero()) {
                return Err(HodgeError::SpectralGapNotSeparated { grade });
            }
            let below = ExactInterval::new(lower.clone(), Rat::zero())?;
            if chain.distinct_root_count(&below)? != 0 {
                return Err(HodgeError::SpectrumNotPositiveSemidefinite { grade });
            }
            lower = Rat::zero();
            continue;
        }
        let mut middle = (&lower + &upper) / &two;
        let mut attempts = 0_usize;
        while chain.vanishes_at(&middle) {
            middle = (&lower + &middle) / &two;
            attempts += 1;
            if attempts > chain.len() + 2 {
                return Err(HodgeError::IsolationSplitUnavailable);
            }
        }
        let below = ExactInterval::new(lower.clone(), middle.clone())?;
        if chain.distinct_root_count(&below)? == 1 {
            upper = middle;
        } else {
            lower = middle;
        }
    }
    Ok(ExactInterval::new(lower, upper)?)
}

/// The coordinates of `Δ_k` grouped into blocks that do not couple.
///
/// Two coordinates are in the same block when a chain of nonzero off-diagonal entries joins them.
/// The operator is block diagonal in this partition, so its characteristic polynomial is the
/// product of the blocks' and every eigenvector splits across them.
fn decoupled_blocks(operator: &ExactRatMatrix) -> Result<Vec<Vec<usize>>, HodgeError> {
    let extent = operator.rows();
    let mut parent: Vec<usize> = (0..extent).collect();
    fn find(parent: &mut [usize], at: usize) -> usize {
        let mut root = at;
        while parent[root] != root {
            root = parent[root];
        }
        let mut cursor = at;
        while parent[cursor] != root {
            let next = parent[cursor];
            parent[cursor] = root;
            cursor = next;
        }
        root
    }
    for row in 0..extent {
        for column in 0..extent {
            if row == column || operator.get(row, column)?.is_zero() {
                continue;
            }
            let (a, b) = (find(&mut parent, row), find(&mut parent, column));
            if a != b {
                parent[a] = b;
            }
        }
    }
    let mut blocks: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    for at in 0..extent {
        let root = find(&mut parent, at);
        blocks.entry(root).or_default().push(at);
    }
    Ok(blocks.into_values().collect())
}

/// The characteristic polynomial of one principal block.
fn block_characteristic(
    operator: &ExactRatMatrix,
    block: &[usize],
) -> Result<RationalPolynomial, HodgeError> {
    let mut rows = Vec::with_capacity(block.len());
    for row in block {
        let mut entries = Vec::with_capacity(block.len());
        for column in block {
            entries.push(operator.get(*row, *column)?.clone());
        }
        rows.push(entries);
    }
    let sub = ExactRatMatrix::shaped(block.len(), block.len(), rows)?;
    Ok(characteristic_polynomial(&sub)?)
}

// -------------------------------------------------------------------------------------------
// the open family
// -------------------------------------------------------------------------------------------

/// **The Hodge reading of a presentation whose incidence is plural.**
///
/// Indexed exactly as [`ConstraintComplexFamily`] is: by the resolutions of the open set, with the
/// two bounds of the 1-cell inclusion order read.
///
/// **A remounted family is held to the agreements between its four readings.** Both bounds are read
/// at the family's grade, under the family's declared metric and condition lineages, and each
/// bound's spectrum is the spectrum of that bound's own operator: its extent is that reading's cell
/// count and its kernel multiplicity is that reading's harmonic dimension — which is exactly the
/// agreement `exact_hodge_spectrum` refuses without. [`Self::bounds_differ_spectrally`] and
/// [`Self::bounds_differ_homologically`] are read off these four, so a wire that pairs one bound's
/// reading with the other's spectrum would make the finding say the opposite of what it measured.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "HodgeFamilyWire")]
pub struct HodgeFamily {
    pub schema: String,
    pub presentation_lineage: String,
    pub grade: u32,
    pub metric_lineage: String,
    pub condition_lineage: String,
    pub open_contacts: Vec<OpenContact>,
    pub open_subsumed_by_inside: Vec<crate::physical_constraint_complex::ConstraintEdge>,
    /// Every open contact refused: the member whose incidence is the presentation's own.
    pub refusing: HodgeReading,
    /// Every open contact founded.
    pub admitting: HodgeReading,
    pub refusing_spectrum: ExactHodgeSpectrum,
    pub admitting_spectrum: ExactHodgeSpectrum,
}

#[derive(Deserialize)]
struct HodgeFamilyWire {
    schema: String,
    presentation_lineage: String,
    grade: u32,
    metric_lineage: String,
    condition_lineage: String,
    open_contacts: Vec<OpenContact>,
    open_subsumed_by_inside: Vec<crate::physical_constraint_complex::ConstraintEdge>,
    refusing: HodgeReading,
    admitting: HodgeReading,
    refusing_spectrum: ExactHodgeSpectrum,
    admitting_spectrum: ExactHodgeSpectrum,
}

impl TryFrom<HodgeFamilyWire> for HodgeFamily {
    type Error = HodgeError;

    fn try_from(wire: HodgeFamilyWire) -> Result<Self, Self::Error> {
        for (bound, reading, spectrum) in [
            ("the refusing bound", &wire.refusing, &wire.refusing_spectrum),
            (
                "the admitting bound",
                &wire.admitting,
                &wire.admitting_spectrum,
            ),
        ] {
            if reading.grade != wire.grade || spectrum.grade != wire.grade {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "Hodge family",
                    relation: "a bound's grade against the family's own",
                    declared: format!("{bound}: {} and {}", reading.grade, spectrum.grade),
                    derived: wire.grade.to_string(),
                });
            }
            if reading.metric_lineage != wire.metric_lineage
                || reading.condition_lineage != wire.condition_lineage
            {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "Hodge family",
                    relation: "a bound's metric and condition lineages against the family's own",
                    declared: format!(
                        "{bound}: {} / {}",
                        reading.metric_lineage, reading.condition_lineage
                    ),
                    derived: format!("{} / {}", wire.metric_lineage, wire.condition_lineage),
                });
            }
            if spectrum.extent != reading.cells {
                return Err(HodgeError::HodgeWireDisagrees {
                    object: "Hodge family",
                    relation: "a bound's spectrum extent against that bound's own cell population",
                    declared: format!("{bound}: {}", spectrum.extent),
                    derived: reading.cells.to_string(),
                });
            }
            if spectrum.kernel_multiplicity != reading.harmonic_dimension {
                return Err(HodgeError::KernelMultiplicityDisagrees {
                    grade: wire.grade,
                    algebraic: spectrum.kernel_multiplicity,
                    geometric: reading.harmonic_dimension,
                });
            }
        }
        Ok(Self {
            schema: wire.schema,
            presentation_lineage: wire.presentation_lineage,
            grade: wire.grade,
            metric_lineage: wire.metric_lineage,
            condition_lineage: wire.condition_lineage,
            open_contacts: wire.open_contacts,
            open_subsumed_by_inside: wire.open_subsumed_by_inside,
            refusing: wire.refusing,
            admitting: wire.admitting,
            refusing_spectrum: wire.refusing_spectrum,
            admitting_spectrum: wire.admitting_spectrum,
        })
    }
}

impl HodgeFamily {
    /// The presentation decides its own incidence: the family is a singleton.
    pub fn is_determinate(&self) -> bool {
        self.open_contacts.is_empty()
    }

    /// `2^n` for `n` open contacts.
    pub fn cardinality(&self) -> BigUint {
        BigUint::from(1_u8) << self.open_contacts.len()
    }

    /// **The finding**: the open class is a spectral question on this presentation.
    pub fn bounds_differ_spectrally(&self) -> bool {
        self.refusing_spectrum.characteristic != self.admitting_spectrum.characteristic
    }

    /// Whether the open class is also a homological question. When this is false and
    /// [`Self::bounds_differ_spectrally`] is true, the contact is invisible to homology and
    /// visible to the spectrum.
    pub fn bounds_differ_homologically(&self) -> bool {
        self.refusing.betti != self.admitting.betti
    }

    /// The two spectral gaps, `(admitting, refusing)`.
    pub fn spectral_gap_bounds(&self) -> (Option<ExactInterval>, Option<ExactInterval>) {
        (
            self.admitting_spectrum.spectral_gap.clone(),
            self.refusing_spectrum.spectral_gap.clone(),
        )
    }
}

/// The reading of one named member of the open family.
pub fn hodge_member(
    complex: &PhysicalConstraintComplex,
    law: &OpenContactLaw,
    metric: &MetricDeclaration,
    boundary: &BoundaryLaw,
    grade: u32,
) -> Result<HodgeReading, HodgeError> {
    let member = graded_constraint_member(complex, law)?;
    let operator = HodgeOperator::from_member(&member, metric, boundary)?;
    hodge_reading(&operator, grade)
}

/// **The family, with its open set and both bounding readings and spectra.**
///
/// Refuses a [`MetricLaw::PerCell`] declaration by name: cell addresses are founded per member, so
/// a per-cell metric does not mean the same thing on the two bounds and silently reusing it would
/// compare two different metrics.
pub fn hodge_family(
    complex: &PhysicalConstraintComplex,
    metric: &MetricDeclaration,
    boundary: &BoundaryLaw,
    grade: u32,
    depth_bound: u32,
) -> Result<HodgeFamily, HodgeError> {
    if metric.law.is_member_local() {
        return Err(HodgeError::PerCellMetricIsMemberLocal);
    }
    let family: ConstraintComplexFamily = graded_constraint_family(complex)?;
    let refusing_operator = HodgeOperator::from_member(&family.refusing, metric, boundary)?;
    let admitting_operator = HodgeOperator::from_member(&family.admitting, metric, boundary)?;
    let refusing = hodge_reading(&refusing_operator, grade)?;
    let admitting = hodge_reading(&admitting_operator, grade)?;
    let refusing_spectrum = exact_hodge_spectrum(&refusing_operator, grade, depth_bound)?;
    let admitting_spectrum = exact_hodge_spectrum(&admitting_operator, grade, depth_bound)?;
    Ok(HodgeFamily {
        schema: HODGE_FAMILY_SCHEMA.to_owned(),
        presentation_lineage: complex.presentation_lineage.clone(),
        grade,
        metric_lineage: metric.lineage.clone(),
        condition_lineage: match boundary {
            BoundaryLaw::Free => "free".to_owned(),
            BoundaryLaw::VanishingOnOccurrences { lineage, .. } => lineage.clone(),
        },
        open_contacts: family.open_contacts,
        open_subsumed_by_inside: family.open_subsumed_by_inside,
        refusing,
        admitting,
        refusing_spectrum,
        admitting_spectrum,
    })
}

// -------------------------------------------------------------------------------------------
// schemas and refusals
// -------------------------------------------------------------------------------------------

pub const HODGE_OPERATOR_SCHEMA: &str = "holonic-engine.hodge-operator.v1";
pub const HODGE_DECOMPOSITION_SCHEMA: &str = "holonic-engine.hodge-decomposition.v1";
pub const HODGE_READING_SCHEMA: &str = "holonic-engine.hodge-reading.v1";
pub const HODGE_SPECTRUM_SCHEMA: &str = "holonic-engine.hodge-spectrum.v1";
pub const MODE_LOCALIZATION_SCHEMA: &str = "holonic-engine.hodge-mode-localization.v1";
pub const HODGE_FAMILY_SCHEMA: &str = "holonic-engine.hodge-family.v1";

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum HodgeError {
    #[error("the graded complex refused: {0}")]
    Algebraic(#[from] CausalAlgebraicError),
    #[error("the exact linear carrier refused: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the exact value carrier refused: {0}")]
    Value(#[from] ExactValueError),
    #[error("the exact polynomial carrier refused: {0}")]
    Polynomial(#[from] ExactPolynomialError),
    #[error("the spectrum owner refused: {0}")]
    Spectrum(#[from] LatticeGaugeRefusal),
    #[error("the graded constraint adapter refused: {0}")]
    Grading(#[from] ConstraintGradingError),
    #[error("the cellular sheaf refused: {0}")]
    CellularSheaf(String),
    #[error(
        "the metric {lineage:?} declares a weight that is not positive (cell {cell:?}, grade {grade:?}); a metric is positive definite or it is not a metric"
    )]
    MetricWeightNotPositive {
        lineage: String,
        cell: Option<CausalCellId>,
        grade: Option<u32>,
    },
    #[error("the declared per-grade metric names no weight for grade {grade}")]
    MetricGradeUnnamed { grade: u32 },
    #[error("the declared metric names no weight for cell {0:?}")]
    MetricCellUnnamed(CausalCellId),
    #[error("the declared metric names cell {0:?}, which the boundary condition has removed")]
    MetricNamesInactiveCell(CausalCellId),
    #[error("cell {0:?} occupies two grades of this operator's coordinate order")]
    CoordinateRepeated(CausalCellId),
    #[error(
        "a per-cell metric is member-local: cell addresses are founded per member of an open family, so the same declaration is a different metric on the two bounds"
    )]
    PerCellMetricIsMemberLocal,
    #[error("the declared boundary set names cell {0:?}, which this complex does not carry")]
    BoundaryCellAbsent(CausalCellId),
    #[error(
        "the declared boundary set is not closed under boundary, so cochains vanishing on it are not preserved by the coboundary and the relative complex it claims does not exist"
    )]
    BoundarySetNotClosed,
    #[error("d∘d is not zero out of grade {grade}")]
    CoboundarySquaredNonzero { grade: u32 },
    #[error(
        "the adjoint characterization W_k δ_k = d_kᵀ W_(k+1) fails at grade {grade}; the codifferential is not the metric adjoint it claims to be"
    )]
    AdjointCharacterizationFails { grade: u32 },
    #[error(
        "comparing against the cellular sheaf needs the free condition: the sheaf owns the whole complex and a relative complex is this module's declaration"
    )]
    CellularSheafComparisonNeedsFreeCondition,
    #[error("a cochain of grade {grade} carries {supplied} coordinates where the grade has {expected}")]
    CochainWidthDisagrees {
        grade: u32,
        expected: usize,
        supplied: usize,
    },
    #[error("the decomposition at grade {grade} does not sum back to the cochain at coordinate {coordinate}")]
    DecompositionDoesNotSum { grade: u32, coordinate: usize },
    #[error("the decomposition at grade {grade} has a nonzero pairing {pairing} in the declared inner product")]
    ComponentsNotOrthogonal { grade: u32, pairing: usize },
    #[error("the harmonic part at grade {grade} is not annihilated by {by}")]
    HarmonicNotAnnihilated { grade: u32, by: &'static str },
    #[error(
        "at grade {grade} the exact {exact}, coexact {coexact} and harmonic {harmonic} dimensions do not sum to the {cells} cells"
    )]
    DimensionsDoNotClose {
        grade: u32,
        exact: usize,
        coexact: usize,
        harmonic: usize,
        cells: usize,
    },
    #[error(
        "at grade {grade} the harmonic dimension {harmonic} disagrees with the Betti number {betti} from the Smith normal form"
    )]
    HarmonicDimensionDisagreesWithBetti {
        grade: u32,
        harmonic: usize,
        betti: usize,
    },
    #[error("the Smith normal form at grade {grade} returned factors that do not divide in order")]
    SmithDivisibilityFails { grade: u32 },
    #[error("the Betti count at grade {grade} underflowed its cell population")]
    BettiUnderflow { grade: u32 },
    #[error("the participation ratio of a zero mode at grade {grade} is not defined")]
    ParticipationOfZeroMode { grade: u32 },
    #[error("grade {grade} carries no active cell, so there is nothing to diagonalize")]
    NothingToDiagonalize { grade: u32 },
    #[error(
        "the isolation at grade {grade} placed {isolated} roots where the squarefree part has {distinct}; a non-real eigenvalue would do this, and a self-adjoint operator has none"
    )]
    SpectrumIncomplete {
        grade: u32,
        isolated: usize,
        distinct: usize,
    },
    #[error("an isolating interval at grade {grade} contains two rational eigenvalues")]
    IsolationHoldsTwoRoots { grade: u32 },
    #[error("the isolating intervals at grade {grade} overlap, so the eigenvalues are not ordered")]
    SpectrumIntervalsOverlap { grade: u32 },
    #[error(
        "at grade {grade} zero has algebraic multiplicity {algebraic} and geometric multiplicity {geometric}; a self-adjoint operator has neither"
    )]
    KernelMultiplicityDisagrees {
        grade: u32,
        algebraic: usize,
        geometric: usize,
    },
    #[error("the spectral gap at grade {grade} is not separated from zero by its isolating interval")]
    SpectralGapNotSeparated { grade: u32 },
    #[error(
        "grade {grade} carries a negative eigenvalue; a Laplacian in a positive definite metric has none, so the declared metric or the incidence is not what it claims"
    )]
    SpectrumNotPositiveSemidefinite { grade: u32 },
    #[error("a refinement width must be positive; a zero width asks for an exact rational that an irrational eigenvalue does not have")]
    RefinementWidthNotPositive,
    #[error("grade {grade} carries no positive eigenvalue, so there is no gap to narrow")]
    NoPositiveEigenvalue { grade: u32 },
    #[error("the isolation exceeded its declared depth bound of {bound} bisections")]
    IsolationDepthExceeded { bound: u32 },
    #[error(
        "the declared isolation depth bound {bound} is past this receiver's ceiling of {ceiling} bisections; the descent is sized by the declaration, so an unbounded declaration is refused by name rather than run"
    )]
    IsolationDepthBoundTooLarge { bound: u32, ceiling: u32 },
    #[error("no rational split point outside the exactly known root population was available")]
    IsolationSplitUnavailable,
    #[error("an isolating interval endpoint is a root, so the sign test cannot decide")]
    IsolationEndpointIsARoot,
    #[error("an isolated root carries no multiplicity in the squarefree decomposition")]
    MultiplicityNotFound,
    #[error(
        "the product of the decoupled blocks' characteristic polynomials at grade {grade} is not the operator's own"
    )]
    BlockProductDisagrees { grade: u32 },
    #[error("no decoupled block carries an isolated eigenvalue at grade {grade}")]
    NoBlockCarriesEigenvalue { grade: u32 },
    #[error(
        "a remounted exact spectrum declares {declared} for {relation}, where the polynomials it \
         carries give {derived}"
    )]
    SpectrumWireDisagrees {
        relation: &'static str,
        declared: String,
        derived: String,
    },
    #[error(
        "a remounted {object} declares {declared} for {relation}, where the chart it carries gives \
         {derived}"
    )]
    HodgeWireDisagrees {
        object: &'static str,
        relation: &'static str,
        declared: String,
        derived: String,
    },
}

#[cfg(test)]
#[path = "hodge_receiver/tests.rs"]
mod tests;
