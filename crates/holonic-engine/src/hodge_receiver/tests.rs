//! The Hodge receiver's own checks.
//!
//! Every law — the declared metric and its refusals, the declared boundary conditions, `d∘d = 0`,
//! the adjoint characterization, the three-way decomposition with its orthogonality, the harmonic
//! dimension against Betti, the exact spectrum with irrational roots isolated by Sturm, the
//! spectral gap as an exact interval, mode localization in both the rational and the interval
//! cases, and the Open-contact family — is checked on synthetic exact complexes that need no
//! fixture and run everywhere. The measured M5 readings come last: they refuse rather than pass
//! when the authenticated release is absent, and the heavy one is marked and ignored by default.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::*;
use crate::EventId;
use crate::algebraic::{CausalChain, ComparativeMultiplicity};
use crate::physical_constraint_complex::{
    ComponentMaterial, ConstraintComponentId, ContactClass, CoordinateBox3, DistanceAperture,
    PairUncertainty, ResidueMaterial,
};
use crate::physical_constraint_grading::OpenResolution;
use crate::rebase_invariants::rebase_invariants;

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn cochain(values: &[i64]) -> Vec<Rat> {
    values.iter().copied().map(integer).collect()
}

/// A complex founded from a declared 1-skeleton and 2-skeleton on `vertices` occurrences.
///
/// Edge `(a, b)` with `a < b` has boundary `+b − a`, which is the hand
/// `physical_constraint_grading` founds. A face `[a, b, c]` with `a < b < c` has boundary
/// `[b,c] − [a,c] + [a,b]`, the alternating hand, and `found_cell` re-derives `∂∂ = 0` at every
/// founding, so a mistake here is a refusal and never a silent wrong complex.
struct Founded {
    complex: GradedCausalComplex,
    vertices: Vec<CausalCellId>,
    edges: Vec<CausalCellId>,
    faces: Vec<CausalCellId>,
}

fn found(vertices: usize, edges: &[(usize, usize)], faces: &[[usize; 3]]) -> Founded {
    let events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let mut vertex_cells = Vec::new();
    for at in 0..vertices {
        vertex_cells.push(
            complex
                .found_cell(format!("v{at}"), events.clone(), 0, CausalChain::default())
                .expect("a vertex founds"),
        );
    }
    let mut edge_cells = Vec::new();
    let mut edge_index = BTreeMap::new();
    for (lower, upper) in edges {
        assert!(lower < upper, "an edge is written in ascending order");
        let mut boundary = CausalChain::default();
        boundary.add_term(vertex_cells[*upper], ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(vertex_cells[*lower], ComparativeMultiplicity::negative(1_u8));
        let cell = complex
            .found_cell(
                format!("e{lower}_{upper}"),
                events.clone(),
                1,
                boundary,
            )
            .expect("an edge founds");
        edge_cells.push(cell);
        edge_index.insert((*lower, *upper), cell);
    }
    let mut face_cells = Vec::new();
    for triple in faces {
        let [a, b, c] = *triple;
        assert!(a < b && b < c, "a face is written in ascending order");
        let mut boundary = CausalChain::default();
        boundary.add_term(edge_index[&(b, c)], ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(edge_index[&(a, c)], ComparativeMultiplicity::negative(1_u8));
        boundary.add_term(edge_index[&(a, b)], ComparativeMultiplicity::positive(1_u8));
        face_cells.push(
            complex
                .found_cell(format!("f{a}_{b}_{c}"), events.clone(), 2, boundary)
                .expect("a face founds"),
        );
    }
    complex.validate().expect("the founded complex stands");
    Founded {
        complex,
        vertices: vertex_cells,
        edges: edge_cells,
        faces: face_cells,
    }
}

/// The path `0 — 1 — 2 — 3`. Its grade-zero Laplacian has the spectrum `0, 2−√2, 2, 2+√2`, which
/// is the smallest exactly presentable graph whose Hodge spectrum is not rational.
fn path_of_four() -> Founded {
    found(4, &[(0, 1), (1, 2), (2, 3)], &[])
}

/// The cycle `0 — 1 — 2 — 3 — 0`. One independent cycle, so `b_1 = 1` and the harmonic
/// 1-cochains are a line whose direction moves with the metric.
fn cycle_of_four() -> Founded {
    found(4, &[(0, 1), (1, 2), (2, 3), (0, 3)], &[])
}

fn unit() -> MetricDeclaration {
    MetricDeclaration::unit("every cell weight one, declared")
}

fn operator(founded: &Founded, metric: &MetricDeclaration) -> HodgeOperator {
    HodgeOperator::found("synthetic", &founded.complex, metric, &BoundaryCondition::Free)
        .expect("the operator founds")
}

// ---------------------------------------------------------------------------------------------
// the declared metric
// ---------------------------------------------------------------------------------------------

/// **A metric is declared or it is refused.** A weight of zero is not a degenerate metric that
/// gets used anyway; it is refused by name with its lineage, because a positive definite inner
/// product is what makes every projection and every positivity claim below true.
#[test]
fn a_metric_weight_that_is_not_positive_is_refused_by_name() {
    let founded = path_of_four();
    let zero = MetricDeclaration::per_grade("a grade weighted zero", [(0, Rat::zero()), (1, Rat::one())]);
    assert!(matches!(
        HodgeOperator::found("synthetic", &founded.complex, &zero, &BoundaryCondition::Free),
        Err(HodgeError::MetricWeightNotPositive { .. })
    ));

    let negative = MetricDeclaration::per_grade(
        "a grade weighted below zero",
        [(0, Rat::one()), (1, integer(-1))],
    );
    assert!(matches!(
        HodgeOperator::found("synthetic", &founded.complex, &negative, &BoundaryCondition::Free),
        Err(HodgeError::MetricWeightNotPositive { .. })
    ));
}

/// A per-grade declaration that does not reach every grade the population occupies is refused with
/// the grade it forgot. There is no fallthrough to one.
#[test]
fn a_metric_that_does_not_cover_the_population_is_refused_with_the_grade_it_forgot() {
    let founded = path_of_four();
    let partial = MetricDeclaration::per_grade("only the vertices", [(0, Rat::one())]);
    assert_eq!(
        HodgeOperator::found("synthetic", &founded.complex, &partial, &BoundaryCondition::Free),
        Err(HodgeError::MetricGradeUnnamed { grade: 1 })
    );
}

/// A per-cell declaration naming a cell the boundary condition has removed is refused: the metric
/// and the active population must be the same object.
#[test]
fn a_metric_naming_an_inactive_cell_is_refused() {
    let founded = path_of_four();
    let condition = BoundaryCondition::VanishingOn {
        lineage: "the first occurrence is held".to_owned(),
        cells: BTreeSet::from([founded.vertices[0]]),
    };
    let weights = founded
        .complex
        .cells()
        .keys()
        .map(|cell| (*cell, Rat::one()))
        .collect::<Vec<_>>();
    let declaration = MetricDeclaration::per_cell("every cell, including the held one", weights);
    assert_eq!(
        HodgeOperator::found("synthetic", &founded.complex, &declaration, &condition),
        Err(HodgeError::MetricNamesInactiveCell(founded.vertices[0]))
    );
}

/// The unit metric is reached by writing it down. `is_unit_valued` reads the weights; the law
/// records that this particular unit metric was *declared* as one.
#[test]
fn the_unit_metric_is_a_declaration_and_not_a_default() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    assert!(operator.metric.is_unit_valued());
    assert_eq!(operator.metric.law, MetricLaw::Unit);
    assert_eq!(operator.metric.lineage, "every cell weight one, declared");

    let by_hand = MetricDeclaration::per_grade("one, spelled per grade", [(0, Rat::one()), (1, Rat::one())]);
    let spelled = operator_of(&founded, &by_hand, &BoundaryCondition::Free);
    assert!(spelled.metric.is_unit_valued());
    assert_ne!(spelled.metric.law, MetricLaw::Unit, "the same operator, a different declaration");
    assert_eq!(
        spelled.laplacian(0).expect("the operator"),
        operator.laplacian(0).expect("the operator"),
        "and the same Laplacian, because the weights agree"
    );
}

fn operator_of(
    founded: &Founded,
    metric: &MetricDeclaration,
    condition: &BoundaryCondition,
) -> HodgeOperator {
    HodgeOperator::found("synthetic", &founded.complex, metric, condition)
        .expect("the operator founds")
}

// ---------------------------------------------------------------------------------------------
// the declared boundary condition
// ---------------------------------------------------------------------------------------------

/// **A boundary set that is not closed under boundary is refused.** Cochains vanishing on it would
/// not be preserved by the coboundary, so the relative complex it claims does not exist.
#[test]
fn a_boundary_set_that_is_not_a_subcomplex_is_refused() {
    let founded = path_of_four();
    let condition = BoundaryCondition::VanishingOn {
        lineage: "an edge without its endpoints".to_owned(),
        cells: BTreeSet::from([founded.edges[0]]),
    };
    assert_eq!(
        HodgeOperator::found("synthetic", &founded.complex, &unit(), &condition),
        Err(HodgeError::BoundarySetNotClosed)
    );
}

/// A boundary set naming a cell the complex does not carry is refused by address rather than
/// silently ignored.
#[test]
fn a_boundary_set_naming_an_absent_cell_is_refused_by_address() {
    let founded = path_of_four();
    let absent = CausalCellId(9_999);
    let condition = BoundaryCondition::VanishingOn {
        lineage: "a cell from somewhere else".to_owned(),
        cells: BTreeSet::from([absent]),
    };
    assert_eq!(
        HodgeOperator::found("synthetic", &founded.complex, &unit(), &condition),
        Err(HodgeError::BoundaryCellAbsent(absent))
    );
}

/// **The relative complex is a different reading of the same incidence.** `P4` is contractible, so
/// its absolute `b_0` is one; holding one endpoint makes the pair acyclic and every harmonic space
/// vanishes. The harmonic dimensions follow the Betti numbers in both readings, which is what
/// makes the declaration a declaration and not a truncation.
#[test]
fn a_declared_dirichlet_condition_reads_the_relative_complex() {
    let founded = path_of_four();
    let free = operator(&founded, &unit());
    assert_eq!(hodge_reading(&free, 0).expect("the reading").harmonic_dimension, 1);
    assert_eq!(hodge_reading(&free, 1).expect("the reading").harmonic_dimension, 0);

    let held = BoundaryCondition::VanishingOn {
        lineage: "the first occurrence is held at zero".to_owned(),
        cells: BTreeSet::from([founded.vertices[0]]),
    };
    let relative = operator_of(&founded, &unit(), &held);
    assert_eq!(relative.extent(0), 3);
    assert_eq!(relative.extent(1), 3);
    let at_zero = hodge_reading(&relative, 0).expect("the reading");
    let at_one = hodge_reading(&relative, 1).expect("the reading");
    assert_eq!(at_zero.harmonic_dimension, 0);
    assert_eq!(at_zero.betti, 0);
    assert_eq!(at_one.harmonic_dimension, 0);
    assert_eq!(at_one.betti, 0);
    assert_eq!(at_zero.condition_lineage, "the first occurrence is held at zero");
}

// ---------------------------------------------------------------------------------------------
// the operator's own laws
// ---------------------------------------------------------------------------------------------

/// **`d∘d = 0` and the adjoint characterization, re-derived rather than asserted.** `validate` runs
/// at every founding; here it is run again against a complex carrying a 2-cell, where the identity
/// is not vacuous.
#[test]
fn the_coboundary_squares_to_zero_and_the_codifferential_is_the_metric_adjoint() {
    let founded = found(3, &[(0, 1), (0, 2), (1, 2)], &[[0, 1, 2]]);
    let metric = MetricDeclaration::per_grade(
        "vertices one, edges two, faces three",
        [(0, Rat::one()), (1, integer(2)), (2, integer(3))],
    );
    let operator = operator_of(&founded, &metric, &BoundaryCondition::Free);
    operator.validate().expect("every law stands");

    let second = operator
        .coboundary(1)
        .expect("d_1")
        .multiply(&operator.coboundary(0).expect("d_0"))
        .expect("the composite");
    assert!(second.entries().iter().all(Zero::is_zero));

    // The adjoint characterization at the owner that states it: `<d x, y>_1 = <x, δ x>_0` for
    // every pair of coordinate directions, defect exactly zero.
    let coboundary = operator.coboundary(0).expect("d_0");
    let codifferential = operator.codifferential(0).expect("delta_0");
    let domain = operator.metric_matrix(0).expect("W_0");
    let codomain = operator.metric_matrix(1).expect("W_1");
    for source in 0..operator.extent(0) {
        for target in 0..operator.extent(1) {
            let mut x = vec![Rat::zero(); operator.extent(0)];
            x[source] = Rat::one();
            let mut y = vec![Rat::zero(); operator.extent(1)];
            y[target] = Rat::one();
            let defect = coboundary
                .adjoint_defect(&codifferential, &domain, &codomain, &x, &y)
                .expect("the defect returns");
            assert!(defect.is_zero(), "coordinate ({source}, {target}) carries a defect");
        }
    }
}

/// **This module's coboundary is `sheaf_diffusion`'s, and so is its unit-metric Laplacian.**
/// The rank-one cellular sheaf on the same complex produces the same matrices entry for entry, so
/// neither the incidence nor the operator is re-founded here.
#[test]
fn the_coboundary_and_the_unit_laplacian_agree_with_the_cellular_sheaf_owner() {
    let founded = found(3, &[(0, 1), (0, 2), (1, 2)], &[[0, 1, 2]]);
    let operator = operator(&founded, &unit());
    for grade in 0..=1 {
        assert!(
            operator
                .agrees_with_cellular_sheaf(&founded.complex, grade)
                .expect("the comparison returns"),
            "grade {grade}"
        );
    }
    // And under the **unit** metric the whole operator is that owner's `hodge_laplacian`, entry
    // for entry — which is the sense in which this module is an adapter and not a second engine.
    let sheaf = super::rank_one_sheaf(&founded.complex).expect("the rank-one sheaf founds");
    for grade in 0..=2 {
        let theirs = sheaf.hodge_laplacian(grade).expect("the sheaf Laplacian");
        let mine = operator.laplacian(grade).expect("this module's Laplacian");
        assert_eq!(theirs.rows(), mine.rows(), "grade {grade}");
        assert_eq!(theirs, mine, "grade {grade}");
    }

    // The comparison is refused under a relative reading, which the sheaf owner does not carry.
    let held = BoundaryCondition::VanishingOn {
        lineage: "held".to_owned(),
        cells: BTreeSet::from([founded.vertices[0]]),
    };
    let relative = operator_of(&founded, &unit(), &held);
    assert_eq!(
        relative.agrees_with_cellular_sheaf(&founded.complex, 0),
        Err(HodgeError::CellularSheafComparisonNeedsFreeCondition)
    );
}

/// The grade-zero Laplacian of a graph under the unit metric is its ordinary graph Laplacian,
/// entry by entry. This is what ties everything below to an object that can be checked by hand.
#[test]
fn the_grade_zero_laplacian_under_the_unit_metric_is_the_graph_laplacian() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let laplacian = operator.laplacian(0).expect("the Laplacian");
    let expected = [
        [1, -1, 0, 0],
        [-1, 2, -1, 0],
        [0, -1, 2, -1],
        [0, 0, -1, 1],
    ];
    for (row, values) in expected.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            assert_eq!(
                laplacian.get(row, column).expect("an entry"),
                &integer(*value),
                "entry ({row}, {column})"
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// the decomposition
// ---------------------------------------------------------------------------------------------

/// **The three components sum back and are mutually orthogonal in the declared inner product.**
/// Checked on a cycle at grade one, where all three components are genuinely nonzero.
#[test]
fn the_three_components_sum_back_and_are_mutually_orthogonal() {
    let founded = cycle_of_four();
    let metric = MetricDeclaration::per_grade(
        "vertices one, edges three halves",
        [(0, Rat::one()), (1, ratio(3, 2))],
    );
    let operator = operator_of(&founded, &metric, &BoundaryCondition::Free);
    let x = cochain(&[5, -2, 7, 1]);
    let decomposition = hodge_decomposition(&operator, 1, &x).expect("the decomposition returns");

    for (at, value) in x.iter().enumerate() {
        assert_eq!(
            &decomposition.exact[at] + &decomposition.coexact[at] + &decomposition.harmonic[at],
            *value
        );
    }
    assert!(decomposition.pairings.iter().all(Zero::is_zero));
    assert!(decomposition.exact.iter().any(|value| !value.is_zero()));
    assert!(decomposition.harmonic.iter().any(|value| !value.is_zero()));
    // The cycle carries no 2-cell, so the coexact part of a 1-cochain is exactly zero and the
    // decomposition is a genuine two-term one. That is a fact about this complex, not a default.
    assert!(decomposition.coexact.iter().all(Zero::is_zero));

    // The exact part really is `d α` for the returned potential.
    let potential = decomposition.exact_potential.clone().expect("a potential");
    assert_eq!(
        operator.coboundary(0).expect("d_0").apply(&potential).expect("applies"),
        decomposition.exact
    );
}

/// A cochain of the wrong width is refused with both extents rather than indexed past.
#[test]
fn a_cochain_of_the_wrong_width_is_refused() {
    let founded = cycle_of_four();
    let operator = operator(&founded, &unit());
    assert_eq!(
        hodge_decomposition(&operator, 1, &cochain(&[1, 2, 3])),
        Err(HodgeError::CochainWidthDisagrees {
            grade: 1,
            expected: 4,
            supplied: 3
        })
    );
}

/// **The decomposition of a complex carrying a 2-cell has all three parts.** A filled triangle's
/// 1-cochains decompose into exact, coexact and nothing else, because `b_1 = 0` there.
#[test]
fn a_filled_triangle_has_no_harmonic_one_cochain() {
    let founded = found(3, &[(0, 1), (0, 2), (1, 2)], &[[0, 1, 2]]);
    let operator = operator(&founded, &unit());
    let decomposition =
        hodge_decomposition(&operator, 1, &cochain(&[3, -1, 4])).expect("the decomposition");
    assert!(decomposition.harmonic.iter().all(Zero::is_zero));
    assert!(decomposition.exact.iter().any(|value| !value.is_zero()));
    assert!(decomposition.coexact.iter().any(|value| !value.is_zero()));
    let reading = hodge_reading(&operator, 1).expect("the reading");
    assert_eq!(reading.harmonic_dimension, 0);
    assert_eq!(reading.exact_dimension, 2);
    assert_eq!(reading.coexact_dimension, 1);
}

// ---------------------------------------------------------------------------------------------
// harmonic dimension against Betti
// ---------------------------------------------------------------------------------------------

/// **`dim ker Δ_k` is the Betti number, and the two are computed by different owners.** The
/// harmonic dimension is a rational row reduction; the Betti number is an integer Smith normal
/// form with divisibility repair. The reading refuses if they disagree, and here they are also
/// compared against `rebase_invariants`, which reduces the same complex independently.
#[test]
fn the_harmonic_dimension_is_the_betti_number_from_the_smith_normal_form() {
    for (name, founded, expected) in [
        ("a path", path_of_four(), vec![1, 0]),
        ("a cycle", cycle_of_four(), vec![1, 1]),
        (
            "a filled triangle",
            found(3, &[(0, 1), (0, 2), (1, 2)], &[[0, 1, 2]]),
            vec![1, 0, 0],
        ),
        (
            "two components",
            found(5, &[(0, 1), (2, 3), (3, 4)], &[]),
            vec![2, 0],
        ),
    ] {
        let operator = operator(&founded, &unit());
        let readings = hodge_readings(&operator).expect("the readings return");
        let measured = readings
            .iter()
            .map(|reading| reading.harmonic_dimension)
            .collect::<Vec<_>>();
        assert_eq!(measured, expected, "{name}");
        for reading in &readings {
            assert_eq!(reading.harmonic_dimension, reading.betti, "{name}");
            assert!(reading.torsion.is_empty(), "{name} carries no torsion");
        }
        let independent = rebase_invariants(&founded.complex, PivotRule::LargestMagnitude)
            .expect("the rebase invariants return");
        assert_eq!(independent.betti_vector(), expected, "{name} against rebase_invariants");
    }
}

/// The three dimensions close on the cell count at every grade: `n_k = rank d_(k−1) + rank d_k +
/// dim ker Δ_k`. This is the decomposition read as a dimension count.
#[test]
fn the_exact_coexact_and_harmonic_dimensions_close_on_the_cell_count() {
    let founded = found(4, &[(0, 1), (0, 2), (1, 2), (2, 3)], &[[0, 1, 2]]);
    let operator = operator(&founded, &unit());
    for reading in hodge_readings(&operator).expect("the readings") {
        assert_eq!(
            reading.exact_dimension + reading.coexact_dimension + reading.harmonic_dimension,
            reading.cells,
            "grade {}",
            reading.grade
        );
    }
}

/// **Torsion is recorded and is invisible to the harmonic space.** The rational Hodge theory reads
/// the free rank; the projective plane's `H_1 = ℤ/2` has Betti zero and one torsion coefficient,
/// and the reading carries both without confusing them.
#[test]
fn torsion_is_retained_beside_a_harmonic_space_that_cannot_see_it() {
    // A one-vertex, one-edge, one-face presentation of `RP^2`'s cellular chain complex:
    // `∂_2 = 2` and `∂_1 = 0`, so `H_1 = ℤ/2` with Betti zero.
    let events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let vertex = complex
        .found_cell("v", events.clone(), 0, CausalChain::default())
        .expect("a vertex founds");
    let mut loop_boundary = CausalChain::default();
    loop_boundary.add_term(vertex, ComparativeMultiplicity::new(1_u8.into(), 1_u8.into()));
    let edge = complex
        .found_cell("loop", events.clone(), 1, loop_boundary)
        .expect("a loop founds");
    let mut face_boundary = CausalChain::default();
    face_boundary.add_term(edge, ComparativeMultiplicity::positive(2_u8));
    complex
        .found_cell("cap", events, 2, face_boundary)
        .expect("the two-fold cap founds");

    let operator = HodgeOperator::found("projective plane", &complex, &unit(), &BoundaryCondition::Free)
        .expect("the operator founds");
    let at_one = hodge_reading(&operator, 1).expect("the reading");
    assert_eq!(at_one.harmonic_dimension, 0);
    assert_eq!(at_one.betti, 0);
    assert_eq!(at_one.torsion, vec![BigInt::from(2)]);
}

// ---------------------------------------------------------------------------------------------
// the metric moves the representative and not the dimension
// ---------------------------------------------------------------------------------------------

/// **Changing the metric moves the harmonic representative and leaves its dimension alone.**
///
/// This is the Lean pair `harmonic_moves_within_class` and `finrank_harmonic_metric_free`: the two
/// harmonic parts of one cocycle differ by an exact cochain — the same cohomology class — while
/// the harmonic dimension is the Betti number under every positive metric.
#[test]
fn a_metric_change_moves_the_harmonic_representative_within_its_class() {
    let founded = cycle_of_four();
    let x = cochain(&[1, 0, 0, 0]);

    let unit_operator = operator(&founded, &unit());
    let weighted = MetricDeclaration::per_cell(
        "the last edge weighted two",
        founded
            .vertices
            .iter()
            .map(|cell| (*cell, Rat::one()))
            .chain(founded.edges.iter().enumerate().map(|(at, cell)| {
                (*cell, if at == 3 { integer(2) } else { Rat::one() })
            })),
    );
    let weighted_operator = operator_of(&founded, &weighted, &BoundaryCondition::Free);

    let first = hodge_decomposition(&unit_operator, 1, &x).expect("the decomposition");
    let second = hodge_decomposition(&weighted_operator, 1, &x).expect("the decomposition");
    assert_ne!(first.harmonic, second.harmonic, "the representative moves");

    assert_eq!(
        hodge_reading(&unit_operator, 1).expect("the reading").harmonic_dimension,
        hodge_reading(&weighted_operator, 1).expect("the reading").harmonic_dimension,
        "the dimension does not"
    );

    // And the move is within the class: the difference is exact. `d_1 = 0` here, so `x` is a
    // cocycle and the statement applies.
    let difference = first
        .harmonic
        .iter()
        .zip(&second.harmonic)
        .map(|(a, b)| a - b)
        .collect::<Vec<_>>();
    let exact = unit_operator.coboundary(0).expect("d_0");
    assert!(
        exact.preimage_fibre(&difference).expect("the fibre returns").is_some(),
        "the two harmonic representatives are cohomologous"
    );
}

// ---------------------------------------------------------------------------------------------
// the spectrum
// ---------------------------------------------------------------------------------------------

/// **The spectrum is held exactly, including the roots that are not rational.**
///
/// `P4`'s grade-zero Laplacian has the spectrum `0, 2−√2, 2, 2+√2`. The two rational eigenvalues
/// come back exactly and completely; the two irrational ones come back as polynomials with Sturm
/// certified isolating intervals, and nothing anywhere is a decimal.
#[test]
fn the_spectrum_of_a_path_carries_its_irrational_eigenvalues_as_isolated_roots() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");

    assert_eq!(spectrum.extent, 4);
    assert_eq!(spectrum.trace, integer(6));
    assert_eq!(
        spectrum.rational_eigenvalues,
        vec![(Rat::zero(), 1), (integer(2), 1)]
    );
    assert_eq!(spectrum.isolated_eigenvalues.len(), 2);
    assert_eq!(spectrum.kernel_multiplicity, 1);
    assert_eq!(spectrum.distinct(), 4);
    assert!(!spectrum.is_completely_rational());

    // The characteristic polynomial is `λ⁴ − 6λ³ + 10λ² − 4λ`, exactly.
    assert_eq!(
        spectrum.characteristic.coefficients(),
        &[Rat::zero(), integer(-4), integer(10), integer(-6), Rat::one()]
    );
    // Four distinct roots, so the squarefree decomposition is a single factor at multiplicity one.
    assert_eq!(spectrum.squarefree.keys().copied().collect::<Vec<_>>(), vec![1]);

    for (root, multiplicity) in &spectrum.isolated_eigenvalues {
        assert_eq!(*multiplicity, 1);
        let interval = &root.isolating_interval;
        let low = root.polynomial.evaluate(&interval.lower);
        let high = root.polynomial.evaluate(&interval.upper);
        assert!(!low.is_zero() && !high.is_zero(), "an endpoint is never a root");
        assert_ne!(low.is_negative(), high.is_negative(), "the interval brackets the root");
        assert_eq!(
            root.certificate.variations_at_lower - root.certificate.variations_at_upper,
            1,
            "the Sturm certificate counts exactly one root"
        );
    }
}

/// **The spectral gap is an exact interval and never a float.** Here it is the irrational `2−√2`,
/// returned with a strictly positive rational lower bound, and its interval brackets the root of
/// `λ² − 4λ + 2` that lies below two.
#[test]
fn the_spectral_gap_of_a_path_is_an_exact_interval_around_an_irrational_eigenvalue() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let gap = spectrum.spectral_gap.clone().expect("a positive eigenvalue exists");

    assert!(gap.lower.is_positive(), "the gap is separated from zero exactly");
    assert!(!gap.is_point(), "the gap is irrational, so no rational equals it");
    // `q(λ) = λ² − 4λ + 2` has `2 − √2` as its smaller root: positive below it, negative above.
    let q = |value: &Rat| value * value - integer(4) * value + integer(2);
    assert!(q(&gap.lower).is_positive());
    assert!(q(&gap.upper).is_negative());
    assert!(gap.upper < integer(2), "and it is the smallest positive eigenvalue");
}

/// **The gap's certificate narrows to any declared width.** An isolating interval is a proof that
/// one root lies inside, not a tight enclosure; comparing two operators' gaps is a separate,
/// declared request, and this is it.
#[test]
fn the_spectral_gap_narrows_to_a_declared_width() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let narrow = refine_spectral_gap(&spectrum, &ratio(1, 1000), DEFAULT_ISOLATION_DEPTH)
        .expect("the refinement returns");
    assert!(&narrow.upper - &narrow.lower <= ratio(1, 1000));
    assert!(narrow.lower.is_positive());
    let q = |value: &Rat| value * value - integer(4) * value + integer(2);
    assert!(q(&narrow.lower).is_positive());
    assert!(q(&narrow.upper).is_negative());
    // `2 − √2 = 0.585786…`, and a certificate of width at most one thousandth around it must lie
    // inside `(0.5847…, 0.5867…)`.
    assert!(narrow.lower > ratio(584, 1000));
    assert!(narrow.upper < ratio(587, 1000));

    // A rational gap is already a point and comes back unchanged.
    let triangle = found(3, &[(0, 1), (0, 2), (1, 2)], &[]);
    let rational = exact_hodge_spectrum(
        &operator_of(&triangle, &unit(), &BoundaryCondition::Free),
        0,
        DEFAULT_ISOLATION_DEPTH,
    )
    .expect("the spectrum");
    assert_eq!(
        refine_spectral_gap(&rational, &ratio(1, 1000), DEFAULT_ISOLATION_DEPTH)
            .expect("the refinement"),
        ExactInterval::point(integer(3))
    );
    assert_eq!(
        refine_spectral_gap(&spectrum, &Rat::zero(), DEFAULT_ISOLATION_DEPTH),
        Err(HodgeError::RefinementWidthNotPositive)
    );
}

/// A rational spectral gap is a **point** interval: the exact eigenvalue, with no width at all.
#[test]
fn a_rational_spectral_gap_is_a_point_interval() {
    let founded = found(3, &[(0, 1), (0, 2), (1, 2)], &[]);
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    assert_eq!(
        spectrum.rational_eigenvalues,
        vec![(Rat::zero(), 1), (integer(3), 2)]
    );
    let gap = spectrum.spectral_gap.clone().expect("a gap");
    assert!(gap.is_point());
    assert_eq!(gap.lower, integer(3));
}

/// **The declared metric changes the spectrum.** Doubling every edge weight halves nothing about
/// the incidence and yet moves `Δ_0`, which is why the metric may not be a default.
#[test]
fn the_declared_metric_moves_the_spectrum() {
    let founded = found(3, &[(0, 1), (0, 2), (1, 2)], &[]);
    let unit_spectrum = exact_hodge_spectrum(&operator(&founded, &unit()), 0, DEFAULT_ISOLATION_DEPTH)
        .expect("the spectrum");
    let weighted = MetricDeclaration::per_grade(
        "vertices two, edges one",
        [(0, integer(2)), (1, Rat::one())],
    );
    let weighted_spectrum = exact_hodge_spectrum(
        &operator_of(&founded, &weighted, &BoundaryCondition::Free),
        0,
        DEFAULT_ISOLATION_DEPTH,
    )
    .expect("the spectrum");
    assert_eq!(
        weighted_spectrum.rational_eigenvalues,
        vec![(Rat::zero(), 1), (ratio(3, 2), 2)],
        "the weight enters the codifferential and halves the nonzero eigenvalue"
    );
    assert_ne!(unit_spectrum.characteristic, weighted_spectrum.characteristic);
    assert_eq!(
        unit_spectrum.kernel_multiplicity, weighted_spectrum.kernel_multiplicity,
        "and the harmonic dimension is unmoved"
    );
}

/// The isolation refuses above its declared depth rather than descending without a bound.
#[test]
fn the_isolation_refuses_above_its_declared_depth() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    assert_eq!(
        exact_hodge_spectrum(&operator, 0, 0),
        Err(HodgeError::IsolationDepthExceeded { bound: 0 })
    );
}

/// **A declared isolation depth past the ceiling is refused, not descended.**
///
/// The descent is sized by the declaration, so a caller-supplied `u32::MAX` used to be accepted
/// and only discovered at the machine's expense — the isolation was a non-tail double recursion,
/// so a large bound over a clustered spectrum put a caller-sized load on the machine stack, which
/// no `Result` can carry. It is now an explicit worklist under a named ceiling, and the
/// declaration itself is refused by name.
#[test]
fn an_isolation_depth_bound_past_the_ceiling_is_refused_rather_than_descended() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    assert_eq!(
        exact_hodge_spectrum(&operator, 0, u32::MAX),
        Err(HodgeError::IsolationDepthBoundTooLarge {
            bound: u32::MAX,
            ceiling: ISOLATION_DEPTH_CEILING,
        })
    );
    // The ceiling itself is admitted, so the refusal is a ceiling and not a narrowing.
    assert!(exact_hodge_spectrum(&operator, 0, ISOLATION_DEPTH_CEILING).is_ok());
    const { assert!(DEFAULT_ISOLATION_DEPTH <= ISOLATION_DEPTH_CEILING) };
}

/// **The worklist isolation returns its intervals ascending and pairwise disjoint.**
///
/// The recursion it replaced descended left before right, which is what put the intervals in
/// order; the worklist takes the left half of every split first for exactly that reason, and this
/// is the check that the conversion kept it. `P4 ⊔ K2` has the grade-zero spectrum
/// `0, 0, 2−√2, 2, 2+√2` and `2`, so the descent splits repeatedly before it isolates.
#[test]
fn the_isolation_returns_its_intervals_ascending_and_disjoint() {
    for founded in [
        path_of_four(),
        found(6, &[(0, 1), (1, 2), (2, 3), (4, 5)], &[]),
    ] {
        let operator = operator(&founded, &unit());
        let spectrum = exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH)
            .expect("the spectrum returns");
        let intervals = spectrum.intervals();
        assert!(intervals.len() > 1);
        for pair in intervals.windows(2) {
            assert!(
                pair[0].upper <= pair[1].lower,
                "the isolation returned {:?} before {:?}",
                pair[0],
                pair[1]
            );
        }
    }
}

/// **An isolated root with no multiplicity in the squarefree decomposition is a refusal.**
///
/// `multiplicity_in` used to answer `0` for a value the decomposition did not carry — a
/// multiplicity of zero is a claim that the value is not an eigenvalue at all, made exactly where
/// the reading has just decided that it is. It now refuses with the same
/// [`HodgeError::MultiplicityNotFound`] its isolated-root counterpart already made.
#[test]
fn a_value_absent_from_the_squarefree_decomposition_refuses_rather_than_reading_zero() {
    // `(x − 1)(x − 2)²`, decomposed: `V₁ = x − 1`, `V₂ = x − 2`.
    let squarefree = BTreeMap::from([
        (
            1_u32,
            RationalPolynomial::new(vec![integer(-1), Rat::one()]),
        ),
        (
            2_u32,
            RationalPolynomial::new(vec![integer(-2), Rat::one()]),
        ),
    ]);
    assert_eq!(multiplicity_in(&squarefree, &integer(1)), Ok(1));
    assert_eq!(multiplicity_in(&squarefree, &integer(2)), Ok(2));
    assert_eq!(
        multiplicity_in(&squarefree, &integer(3)),
        Err(HodgeError::MultiplicityNotFound),
        "three is a root of neither factor, and a zero here would be a claim that it is not an \
         eigenvalue"
    );
}

/// A grade with no active cell has nothing to diagonalize, which is a refusal and not an empty
/// spectrum that a reader might take for a result.
#[test]
fn a_grade_with_no_active_cell_refuses_to_be_diagonalized() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    assert_eq!(
        exact_hodge_spectrum(&operator, 2, DEFAULT_ISOLATION_DEPTH),
        Err(HodgeError::NothingToDiagonalize { grade: 2 })
    );
}

// ---------------------------------------------------------------------------------------------
// mode localization
// ---------------------------------------------------------------------------------------------

/// **Where the eigenvalue is rational the localization is exact.**
///
/// `K2 ⊔ P3` has the grade-zero spectrum `0, 0, 1, 2, 3`. The eigenvalue `2` belongs to the two
/// occurrence component and the eigenvalue `1` to the three occurrence one, and the receiver says
/// exactly which cells carry each — the support is a property of the eigenspace, and the
/// participation ratio is exactly two for a mode spread evenly over two cells.
#[test]
fn mode_localization_is_exact_where_the_eigenvalue_is_rational() {
    let founded = found(5, &[(0, 1), (2, 3), (3, 4)], &[]);
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    assert!(spectrum.is_completely_rational());
    assert_eq!(
        spectrum.rational_eigenvalues,
        vec![
            (Rat::zero(), 2),
            (Rat::one(), 1),
            (integer(2), 1),
            (integer(3), 1)
        ]
    );

    let at = |value: Rat| {
        spectrum
            .localization
            .iter()
            .find(|mode| mode.eigenvalue == EigenvalueReading::Rational(value.clone()))
            .cloned()
            .expect("the eigenvalue is localized")
    };

    let two = at(integer(2));
    assert_eq!(two.certificate, LocalizationCertificate::ExactEigenspace);
    assert_eq!(two.support, vec![founded.vertices[0], founded.vertices[1]]);
    assert_eq!(two.participation, vec![integer(2)]);

    let one = at(Rat::one());
    assert_eq!(one.support, vec![founded.vertices[2], founded.vertices[4]]);
    assert_eq!(one.participation, vec![integer(2)]);

    let three = at(integer(3));
    assert_eq!(
        three.support,
        vec![founded.vertices[2], founded.vertices[3], founded.vertices[4]]
    );
    // `(1, −2, 1)`: mass `6`, fourth moment `18`, participation `36/18 = 2`.
    assert_eq!(three.participation, vec![integer(2)]);

    let harmonic = at(Rat::zero());
    assert_eq!(harmonic.multiplicity, 2);
    assert_eq!(harmonic.support.len(), 5, "each component's indicator is harmonic");
}

/// **A concentrated mode and a spread one are separated by an exact rational.**
#[test]
fn the_participation_ratio_separates_a_concentrated_mode_from_a_spread_one() {
    // A star on four occurrences: one centre, three leaves. `Δ_0` has eigenvalues `0, 1, 1, 4`.
    // The `λ = 1` eigenspace lives on the leaves alone — three cells — and its canonical basis
    // vectors are two-cell differences, so participation is exactly two while the `λ = 4` mode
    // spreads over all four with participation `16/10`.
    let founded = found(4, &[(0, 1), (0, 2), (0, 3)], &[]);
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let at = |value: Rat| {
        spectrum
            .localization
            .iter()
            .find(|mode| mode.eigenvalue == EigenvalueReading::Rational(value.clone()))
            .cloned()
            .expect("the eigenvalue is localized")
    };
    let leaves = at(Rat::one());
    assert_eq!(leaves.multiplicity, 2);
    assert_eq!(
        leaves.support,
        vec![founded.vertices[1], founded.vertices[2], founded.vertices[3]],
        "the centre carries no part of this eigenspace"
    );
    assert_eq!(leaves.participation, vec![integer(2), integer(2)]);

    let spread = at(integer(4));
    assert_eq!(spread.support.len(), 4);
    // `(−3, 1, 1, 1)`: mass `12`, fourth moment `81 + 3 = 84`, participation `144/84 = 12/7`.
    assert_eq!(spread.participation, vec![ratio(12, 7)]);
}

/// **Where the eigenvalue is not rational the statement is interval-certified.**
///
/// `P4 ⊔ K2` decouples into two blocks. The irrational eigenvalues `2 ± √2` belong to the path
/// alone, and the receiver certifies that by the sign of each block's squarefree characteristic
/// factor at the two rational endpoints of the isolating interval — no eigenvector is written
/// down, and none is needed for the statement.
#[test]
fn mode_localization_is_interval_certified_where_the_eigenvalue_is_not_rational() {
    let founded = found(6, &[(0, 1), (1, 2), (2, 3), (4, 5)], &[]);
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    assert_eq!(spectrum.kernel_multiplicity, 2);
    assert_eq!(spectrum.isolated_eigenvalues.len(), 2);

    let irrational = spectrum
        .localization
        .iter()
        .filter(|mode| !mode.eigenvalue.is_rational())
        .collect::<Vec<_>>();
    assert_eq!(irrational.len(), 2);
    for mode in irrational {
        let LocalizationCertificate::IntervalBlocks { carrying, blocks } = &mode.certificate else {
            panic!("an irrational eigenvalue carries an interval certificate");
        };
        assert_eq!(*blocks, 2, "the operator decouples into two blocks");
        assert_eq!(carrying.len(), 1, "exactly one block carries this eigenvalue");
        assert_eq!(
            carrying[0],
            vec![
                founded.vertices[0],
                founded.vertices[1],
                founded.vertices[2],
                founded.vertices[3]
            ],
            "and it is the path, not the isolated edge"
        );
        assert!(mode.participation.is_empty(), "no eigenvector is claimed");
    }
}

// ---------------------------------------------------------------------------------------------
// the Open-contact family
// ---------------------------------------------------------------------------------------------

fn undecided_uncertainty(left: usize, right: usize) -> BTreeMap<(u32, u32), PairUncertainty> {
    let mut result = BTreeMap::new();
    for row in 1..=left as u32 {
        for column in 1..=right as u32 {
            result.insert(
                (row, column),
                PairUncertainty {
                    source_lineage: "exact-testimony".to_owned(),
                    row_given_column_bits: 0x3c00,
                    column_given_row_bits: 0x3c00,
                    row_given_column: ExactInterval::point(integer(1)),
                    column_given_row: ExactInterval::point(integer(1)),
                    row_given_column_ulp: ratio(1, 1024),
                    column_given_row_ulp: ratio(1, 1024),
                },
            );
        }
    }
    result
}

/// One presentation carrying exactly one open contact, whose admission closes a triangle.
///
/// The same presentation `rigidity_receiver`'s family test uses, so the two receivers are read on
/// one object: `d²(1,3) ∈ [1, 121/100]` is inside an aperture of `51/10` and `d²(2,3) ∈
/// [5, 521/100]` straddles it.
fn undecided_presentation() -> PhysicalConstraintComplex {
    let material = vec![
        ComponentMaterial {
            lineage: "chain".to_owned(),
            residues: vec![
                ResidueMaterial {
                    source_ordinal: 1,
                    monomer: "A".to_owned(),
                    position: CoordinateBox3::point(integer(0), integer(0), integer(0)),
                },
                ResidueMaterial {
                    source_ordinal: 2,
                    monomer: "B".to_owned(),
                    position: CoordinateBox3::point(integer(2), integer(0), integer(0)),
                },
            ],
        },
        ComponentMaterial {
            lineage: "partner".to_owned(),
            residues: vec![ResidueMaterial {
                source_ordinal: 1,
                monomer: "C".to_owned(),
                position: CoordinateBox3 {
                    x: ExactInterval::point(integer(0)),
                    y: ExactInterval::new(integer(1), ratio(11, 10)).expect("ordered"),
                    z: ExactInterval::point(integer(0)),
                },
            }],
        },
    ];
    let mut complex = PhysicalConstraintComplex::found("undecided partner", EventId(1), material)
        .expect("the presentation founds");
    let aperture = DistanceAperture {
        lineage: "squared distance at or below fifty-one tenths".to_owned(),
        squared: ratio(51, 10),
    };
    let left = ConstraintComponentId(1);
    let right = ConstraintComponentId(2);
    let enacted = {
        let left_vertices = complex.component(left).expect("component").vertices.clone();
        let right_vertices = complex.component(right).expect("component").vertices.clone();
        left_vertices
            .iter()
            .flat_map(|a| {
                let aperture = &aperture;
                let complex = &complex;
                right_vertices.iter().map(move |b| {
                    aperture.classify(
                        &complex.vertices[a]
                            .position
                            .squared_distance(&complex.vertices[b].position),
                    )
                })
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(
        enacted,
        vec![ContactClass::Inside, ContactClass::Open],
        "one decided contact and one genuinely undecided one"
    );
    complex
        .found_contact_family(left, right, aperture, &enacted, &undecided_uncertainty(2, 1))
        .expect("the family founds");
    complex
}

/// **The finding: an open contact can be invisible to homology and visible to the spectrum.**
///
/// The two bounds of the family have the same Betti numbers — both are connected and both have no
/// independent cycle — and different characteristic polynomials: the refusing member is a path
/// with spectral gap exactly `1` and the admitting member is a filled triangle with spectral gap
/// exactly `3`. Neither bound may be taken for the answer, and a receiver that read only the
/// homology would report the open class as bookkeeping. It is not.
#[test]
fn the_open_family_bounds_differ_spectrally_while_their_betti_numbers_agree() {
    let complex = undecided_presentation();
    let family = hodge_family(
        &complex,
        &unit(),
        &BoundaryLaw::Free,
        0,
        DEFAULT_ISOLATION_DEPTH,
    )
    .expect("the family returns");

    assert!(!family.is_determinate());
    assert_eq!(family.open_contacts.len(), 1);
    assert_eq!(family.cardinality(), BigUint::from(2_u8));
    assert!(family.open_subsumed_by_inside.is_empty());

    assert_eq!(family.refusing.cells, 3);
    assert_eq!(family.admitting.cells, 3);
    assert_eq!(family.refusing.betti, 1);
    assert_eq!(family.admitting.betti, 1);
    assert!(!family.bounds_differ_homologically());

    assert!(family.bounds_differ_spectrally());
    assert_eq!(
        family.refusing_spectrum.rational_eigenvalues,
        vec![(Rat::zero(), 1), (Rat::one(), 1), (integer(3), 1)],
        "the refusing member is the path on three occurrences"
    );
    assert_eq!(
        family.admitting_spectrum.rational_eigenvalues,
        vec![(Rat::zero(), 1), (integer(3), 2)],
        "the admitting member is the triangle, and admitting the contact closes its two-cell"
    );
    let (admitting_gap, refusing_gap) = family.spectral_gap_bounds();
    assert_eq!(refusing_gap.expect("a gap").lower, Rat::one());
    assert_eq!(admitting_gap.expect("a gap").lower, integer(3));
}

/// A named member is reachable by declaring the resolution, and a declaration that does not name
/// every open contact exactly once refuses through the adapter that owns that law.
#[test]
fn a_declared_resolution_selects_a_member_and_an_incomplete_one_refuses() {
    let complex = undecided_presentation();
    let family = graded_constraint_family(&complex).expect("the graded family returns");
    let open = family.open_contacts[0].edge;

    let admitted = hodge_member(
        &complex,
        &OpenContactLaw::Declared(OpenResolution::declared([(open, true)])),
        &unit(),
        &BoundaryLaw::Free,
        1,
    )
    .expect("the declared member returns");
    assert_eq!(admitted.cells, 3, "three one-cells once the contact is founded");

    let refused = hodge_member(
        &complex,
        &OpenContactLaw::Declared(OpenResolution::declared([])),
        &unit(),
        &BoundaryLaw::Free,
        0,
    );
    assert!(
        matches!(refused, Err(HodgeError::Grading(_))),
        "a resolution that names no open contact is refused by the grading owner, not defaulted"
    );
}

/// **A per-cell metric cannot cross a family.** Cell addresses are founded per member, so the same
/// declaration would silently be two different metrics on the two bounds; it is refused by name.
#[test]
fn a_per_cell_metric_is_refused_for_a_family() {
    let complex = undecided_presentation();
    let declaration = MetricDeclaration::per_cell("member-local", [(CausalCellId(1), Rat::one())]);
    assert_eq!(
        hodge_family(
            &complex,
            &declaration,
            &BoundaryLaw::Free,
            0,
            DEFAULT_ISOLATION_DEPTH
        ),
        Err(HodgeError::PerCellMetricIsMemberLocal)
    );
}

/// A boundary condition declared by occurrence address resolves the same way against both bounds,
/// which is what lets a relative reading be taken over a plural incidence at all.
#[test]
fn an_occurrence_addressed_boundary_condition_crosses_the_family() {
    let complex = undecided_presentation();
    let law = BoundaryLaw::VanishingOnOccurrences {
        lineage: "the first occurrence is held at zero".to_owned(),
        occurrences: BTreeSet::from([ConstraintVertexId(1)]),
    };
    let family = hodge_family(&complex, &unit(), &law, 0, DEFAULT_ISOLATION_DEPTH)
        .expect("the family returns");
    assert_eq!(family.refusing.cells, 2);
    assert_eq!(family.admitting.cells, 2);
    assert_eq!(family.refusing.harmonic_dimension, 0);
    assert_eq!(family.admitting.harmonic_dimension, 0);
    assert!(family.bounds_differ_spectrally());
}

// ---------------------------------------------------------------------------------------------
// remounting
// ---------------------------------------------------------------------------------------------

/// **A remounted operator is re-checked, not trusted.** `Deserialize` runs no constructor, so a
/// chart whose metric no longer covers the population is refused by the reading rather than
/// indexed past.
#[test]
fn a_remounted_operator_with_a_poisoned_metric_refuses_rather_than_reading() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let round_trip: HodgeOperator =
        serde_json::from_str(&serde_json::to_string(&operator).expect("serializes"))
            .expect("deserializes");
    assert_eq!(round_trip, operator);

    let mut wire: serde_json::Value = serde_json::to_value(&operator).expect("serializes");
    let weights = wire["metric"]["weights"]
        .as_object_mut()
        .expect("the resolved weights are a map");
    let key = weights.keys().next().cloned().expect("at least one weight");
    weights.remove(&key);
    let poisoned: HodgeOperator = serde_json::from_value(wire).expect("deserializes");
    assert!(
        matches!(
            hodge_reading(&poisoned, 0),
            Err(HodgeError::MetricCellUnnamed(_))
        ),
        "a metric that no longer covers the population is refused by name"
    );
}

/// A reading and a spectrum both remount from their serialized charts unchanged.
#[test]
fn a_reading_and_a_spectrum_remount_from_their_serialized_charts() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let reading = hodge_reading(&operator, 0).expect("the reading");
    let wire = serde_json::to_string(&reading).expect("serializes");
    let remounted: HodgeReading = serde_json::from_str(&wire).expect("deserializes");
    assert_eq!(remounted, reading);

    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum");
    let wire = serde_json::to_string(&spectrum).expect("serializes");
    let remounted: ExactHodgeSpectrum = serde_json::from_str(&wire).expect("deserializes");
    assert_eq!(remounted, spectrum);
}

// ---------------------------------------------------------------------------------------------
// the wires
// ---------------------------------------------------------------------------------------------
//
// `Deserialize` runs no constructor, so every object here that carries a certificate or an
// invariant is closed at its own wire. Each test builds a lawful value through the real
// constructor, checks it round-trips unchanged, and then hands the wire a hand-tampered chart the
// derived implementation used to accept, asserting the refusal by the words of its own species.

/// A lawful value's serialized chart, ready to be tampered with.
fn chart<T: serde::Serialize>(value: &T) -> serde_json::Value {
    serde_json::to_value(value).expect("the chart serializes")
}

/// A rational on the wire. `Rat` is `[numerator, denominator]` over `BigInt`s that are themselves
/// `[sign, [digits]]`, so a declared value is serialized rather than written as a literal.
fn rational(value: &Rat) -> serde_json::Value {
    serde_json::to_value(value).expect("a rational serializes")
}

fn refusal_of<T: serde::de::DeserializeOwned>(hostile: serde_json::Value) -> String {
    serde_json::from_value::<T>(hostile)
        .err()
        .expect("the tampered chart is refused")
        .to_string()
}

/// **A remounted law is refused when it declares a weight that is not a weight.** Positivity needs
/// no population to decide, so it is decided at the declaration rather than at the first resolution
/// that happens to name that grade.
#[test]
fn a_metric_law_wire_is_refused_when_a_declared_weight_is_not_positive() {
    let law = MetricDeclaration::per_grade("declared", [(0, Rat::one()), (1, integer(2))]).law;
    let remounted: MetricLaw =
        serde_json::from_value(chart(&law)).expect("a lawful chart remounts");
    assert_eq!(remounted, law);

    let mut hostile = chart(&law);
    hostile["PerGrade"]["0"] = rational(&Rat::zero());
    let refusal = refusal_of::<MetricLaw>(hostile);
    assert!(
        refusal.contains("weight that is not positive"),
        "the refusal names the disagreement: {refusal}"
    );

    let cell_law = MetricDeclaration::per_cell("declared", [(CausalCellId(1), Rat::one())]).law;
    let mut hostile = chart(&cell_law);
    hostile["PerCell"]["1"] = rational(&integer(-1));
    let refusal = refusal_of::<MetricLaw>(hostile);
    assert!(
        refusal.contains("weight that is not positive"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted metric is held to its own law.** A unit law resolves to the constant one and a
/// per-cell law resolves to exactly the map it declares, so a resolution that disagrees with the
/// law travelling beside it is refused rather than carried into every weight the operator reads.
#[test]
fn a_cell_metric_wire_is_refused_when_it_does_not_resolve_its_own_law() {
    let founded = path_of_four();
    let metric = operator(&founded, &unit()).metric;
    let remounted: CellMetric =
        serde_json::from_value(chart(&metric)).expect("a lawful chart remounts");
    assert_eq!(remounted, metric);

    let key = chart(&metric)["weights"]
        .as_object()
        .expect("the resolved weights are a map")
        .keys()
        .next()
        .cloned()
        .expect("at least one weight");

    let mut hostile = chart(&metric);
    hostile["weights"][&key] = rational(&integer(2));
    let refusal = refusal_of::<CellMetric>(hostile);
    assert!(
        refusal.contains("unit law's resolved weight"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&metric);
    hostile["weights"][&key] = rational(&Rat::zero());
    let refusal = refusal_of::<CellMetric>(hostile);
    assert!(
        refusal.contains("weight that is not positive"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted decomposition re-adds its own three parts.** The sum and the three vanishing
/// pairings are the receipts the type exists to carry, and they are re-derived rather than read.
#[test]
fn a_decomposition_wire_re_adds_its_own_three_parts() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let decomposition = hodge_decomposition(&operator, 0, &cochain(&[1, 0, 0, 0]))
        .expect("the decomposition returns");
    let remounted: HodgeDecomposition =
        serde_json::from_value(chart(&decomposition)).expect("a lawful chart remounts");
    assert_eq!(remounted, decomposition);

    let mut hostile = chart(&decomposition);
    hostile["harmonic"][0] = rational(&integer(9));
    let refusal = refusal_of::<HodgeDecomposition>(hostile);
    assert!(
        refusal.contains("does not sum back to the cochain"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&decomposition);
    hostile["pairings"][1] = rational(&ratio(1, 3));
    let refusal = refusal_of::<HodgeDecomposition>(hostile);
    assert!(
        refusal.contains("nonzero pairing"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted reading re-derives every count it can.** The Betti number, the rank of the
/// exhibited harmonic basis, the torsion coefficients' own normal form and the localization beside
/// them are each re-read from what the chart already carries.
#[test]
fn a_reading_wire_re_derives_its_counts_and_its_basis() {
    // Two components, so the harmonic space is a plane and a dependent "basis" is a real forgery.
    let founded = found(4, &[(0, 1), (2, 3)], &[]);
    let operator = operator(&founded, &unit());
    let reading = hodge_reading(&operator, 0).expect("the reading returns");
    assert_eq!(reading.harmonic_dimension, 2);
    let remounted: HodgeReading =
        serde_json::from_value(chart(&reading)).expect("a lawful chart remounts");
    assert_eq!(remounted, reading);

    let mut hostile = chart(&reading);
    hostile["betti"] = serde_json::json!(3);
    let refusal = refusal_of::<HodgeReading>(hostile);
    assert!(
        refusal.contains("disagrees with the Betti number"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&reading);
    hostile["harmonic_basis"][1] = chart(&reading.harmonic_basis[0]);
    let refusal = refusal_of::<HodgeReading>(hostile);
    assert!(
        refusal.contains("rank of the exhibited harmonic basis"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&reading);
    hostile["torsion"] = chart(&vec![BigInt::one()]);
    let refusal = refusal_of::<HodgeReading>(hostile);
    assert!(
        refusal.contains("torsion coefficient"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&reading);
    hostile["harmonic_localization"]["grade"] = serde_json::json!(1);
    let refusal = refusal_of::<HodgeReading>(hostile);
    assert!(
        refusal.contains("harmonic localization"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted localization is held to which of the two statements it makes.** An exact
/// eigenspace is solved for only at a rational eigenvalue; a containment names no eigenvector and
/// carries no participation vector.
#[test]
fn a_mode_localization_wire_is_refused_when_its_certificate_leaves_its_eigenvalue() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let isolated = spectrum
        .localization
        .iter()
        .find(|mode| !mode.eigenvalue.is_rational())
        .cloned()
        .expect("the path of four carries an irrational eigenvalue");
    let remounted: ModeLocalization =
        serde_json::from_value(chart(&isolated)).expect("a lawful chart remounts");
    assert_eq!(remounted, isolated);

    let mut hostile = chart(&isolated);
    hostile["certificate"] = serde_json::json!("ExactEigenspace");
    let refusal = refusal_of::<ModeLocalization>(hostile);
    assert!(
        refusal.contains("solved for only at a rational eigenvalue"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&isolated);
    hostile["support"] = serde_json::json!([]);
    let refusal = refusal_of::<ModeLocalization>(hostile);
    assert!(
        refusal.contains("union of the carrying blocks"),
        "the refusal names the disagreement: {refusal}"
    );

    let rational_mode = spectrum
        .localization
        .iter()
        .find(|mode| mode.eigenvalue.is_rational())
        .cloned()
        .expect("zero is a rational eigenvalue of every graph Laplacian");
    let mut hostile = chart(&rational_mode);
    hostile["participation"] = serde_json::json!([]);
    let refusal = refusal_of::<ModeLocalization>(hostile);
    assert!(
        refusal.contains("one per exhibited basis vector"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted spectrum re-derives almost all of itself.** This is the object that genuinely
/// travels: `refine_spectral_gap` bisects against the `radical` it carries and [`HodgeFamily`]
/// compares two of them, so a substituted radical, a forged trace, a multiplicity that no longer
/// closes on the extent and a gap that is not the least non-zero eigenvalue's are each refused.
#[test]
fn a_spectrum_wire_re_derives_its_radical_its_trace_and_its_multiplicities() {
    let founded = path_of_four();
    let operator = operator(&founded, &unit());
    let spectrum =
        exact_hodge_spectrum(&operator, 0, DEFAULT_ISOLATION_DEPTH).expect("the spectrum returns");
    let remounted: ExactHodgeSpectrum =
        serde_json::from_value(chart(&spectrum)).expect("a lawful chart remounts");
    assert_eq!(remounted, spectrum);

    let mut hostile = chart(&spectrum);
    hostile["radical"]["coefficients"][0] = chart(&BigInt::from(7));
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("primitive integer form of the squarefree part"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["trace"] = rational(&integer(99));
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("subleading coefficient"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["rational_eigenvalues"][0][1] = serde_json::json!(2);
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("multiplicity against the squarefree decomposition"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["kernel_multiplicity"] = serde_json::json!(2);
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("geometric multiplicity"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["spectral_gap"] = serde_json::Value::Null;
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("absent exactly when nothing but zero"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    let listed = chart(&spectrum.isolated_eigenvalues);
    hostile["isolated_eigenvalues"] =
        serde_json::Value::Array(listed.as_array().expect("a list").iter().rev().cloned().collect());
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("listed ascending"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["squarefree"] = serde_json::json!({});
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("re-multiplied against the characteristic polynomial"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&spectrum);
    hostile["extent"] = serde_json::json!(5);
    let refusal = refusal_of::<ExactHodgeSpectrum>(hostile);
    assert!(
        refusal.contains("monic of the declared extent"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted family keeps each bound's reading with that bound's own spectrum.** Both findings
/// the type exists to report are read off those four objects, so a chart that crosses them would
/// make the finding say the opposite of what was measured.
#[test]
fn a_family_wire_keeps_each_bound_with_its_own_spectrum() {
    let complex = undecided_presentation();
    let family = hodge_family(&complex, &unit(), &BoundaryLaw::Free, 0, DEFAULT_ISOLATION_DEPTH)
        .expect("the family returns");
    let remounted: HodgeFamily =
        serde_json::from_value(chart(&family)).expect("a lawful chart remounts");
    assert_eq!(remounted, family);

    let mut hostile = chart(&family);
    hostile["grade"] = serde_json::json!(1);
    let refusal = refusal_of::<HodgeFamily>(hostile);
    assert!(
        refusal.contains("bound's grade against the family's own"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&family);
    hostile["metric_lineage"] = serde_json::json!("another metric entirely");
    let refusal = refusal_of::<HodgeFamily>(hostile);
    assert!(
        refusal.contains("metric and condition lineages"),
        "the refusal names the disagreement: {refusal}"
    );

    // A reading of another complex entirely, with the family's own grade and lineages, so nothing
    // below the family notices: only the family holds the spectrum beside the reading it measured.
    let foreign = hodge_reading(&operator(&path_of_four(), &unit()), 0).expect("the reading");
    assert_eq!(foreign.grade, family.grade);
    assert_eq!(foreign.metric_lineage, family.metric_lineage);
    assert_ne!(foreign.cells, family.refusing_spectrum.extent);
    let mut hostile = chart(&family);
    hostile["refusing"] = chart(&foreign);
    let refusal = refusal_of::<HodgeFamily>(hostile);
    assert!(
        refusal.contains("own cell population"),
        "the refusal names the disagreement: {refusal}"
    );
}

// ---------------------------------------------------------------------------------------------
// the measured M5 structures
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the receiver is measured on, declared rather than inferred. This is the same
/// window `rigidity_receiver` measures, so the two receivers read one object.
const WINDOW: usize = 24;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;

const M5_STRUCTURES: [(&str, &str); 3] = [
    ("designed-free", "designed-free-rbx1.cif"),
    ("protenix-free-seed2", "ptxv2-free-rbx1-seed2.cif"),
    ("protenix-cul1-seed0", "ptxv2-cul1-rbx1-seed0.cif"),
];

fn structure_root() -> PathBuf {
    std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT))
}

fn require_structure_root() -> PathBuf {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured Hodge reading cannot \
         be taken, and this test refuses to report success without taking it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory \
         carrying designed-free-rbx1.cif, ptxv2-free-rbx1-seed2.cif and \
         ptxv2-cul1-rbx1-seed0.cif. Every law this module owns is checked without any fixture by \
         the synthetic tests above.",
        root.display()
    );
    root
}


fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// The contact complex of one window: the backbone steps plus every pair inside the aperture.
///
/// The 2-cells are every triple all of whose three 1-cells stand — the same founding law
/// `physical_constraint_grading` applies to a contact family, replayed on one component.
fn contact_complex(window: &[Vec<Rat>], with_faces: bool) -> Founded {
    let aperture = integer(CONTACT_SQUARED);
    let mut edges = Vec::new();
    for left in 0..WINDOW {
        for right in (left + 1)..WINDOW {
            if right == left + 1 || squared_distance(&window[left], &window[right]) <= aperture {
                edges.push((left, right));
            }
        }
    }
    let present: BTreeSet<(usize, usize)> = edges.iter().copied().collect();
    let mut faces = Vec::new();
    if with_faces {
        for a in 0..WINDOW {
            for b in (a + 1)..WINDOW {
                for c in (b + 1)..WINDOW {
                    if present.contains(&(a, b)) && present.contains(&(a, c)) && present.contains(&(b, c))
                    {
                        faces.push([a, b, c]);
                    }
                }
            }
        }
    }
    found(WINDOW, &edges, &faces)
}



// ---------------------------------------------------------------------------------------------
// the operator as the core complex and its metric storage (plan phase 4)
// ---------------------------------------------------------------------------------------------

/// **The operator's `d`, weighted adjoint and Laplacian are the core complex's under the metric
/// storage.** On the free condition the operator's chart is the graded complex's own chart; its
/// `d_k` is the core coboundary, its `δ_k` the core `codifferential(k, W_k, W_(k+1))` and its
/// `Δ_k` the core `hodge_laplacian`, entry for entry. The Kirchhoff structure of the chart's `d₀`
/// is Dirac and passes Tellegen (`Holon/Dirac.lean::tellegen`). On a relative condition the chart
/// is the relative complex, whose Betti numbers are the relative Hodge reading's.
#[test]
fn the_operator_is_the_core_complex_with_its_metric_as_storage() {
    let founded = found(4, &[(0, 1), (0, 2), (1, 2), (2, 3)], &[[0, 1, 2]]);
    let metric = MetricDeclaration::per_grade(
        "vertices two, edges three halves, faces five",
        [(0, integer(2)), (1, ratio(3, 2)), (2, integer(5))],
    );
    let operator = operator_of(&founded, &metric, &BoundaryCondition::Free);
    let chart = operator.core_chart().expect("the chart stands");
    assert_eq!(
        &chart,
        &founded
            .complex
            .core_chart()
            .expect("the complex's own chart"),
        "the free operator's chart is its complex's"
    );
    let core = chart.complex();
    let storages = operator.metric_storages().expect("every grade's storage");
    assert_eq!(storages.len(), 3);
    for grade in 0..=2_u32 {
        let k = grade as usize;
        assert_eq!(chart.cells(k), operator.cells(grade));
        if grade < 2 {
            assert_eq!(
                core.coboundary(k).unwrap().expect("d_k"),
                operator.coboundary(grade).unwrap()
            );
            assert_eq!(
                core.codifferential(k, &storages[k], &storages[k + 1])
                    .unwrap(),
                operator.codifferential(grade).unwrap()
            );
        }
        assert_eq!(
            core.hodge_laplacian(k, &storages).unwrap(),
            operator.laplacian(grade).unwrap()
        );
        assert_eq!(
            core.betti(k).unwrap(),
            hodge_reading(&operator, grade).unwrap().betti
        );
    }
    let kirchhoff = core.kirchhoff().expect("the Kirchhoff structure is Dirac");
    assert!(kirchhoff.tellegen().expect("Tellegen on the structure") > 0);
    let sheaf = rank_one_sheaf(&founded.complex).expect("the rank-one sheaf");
    assert_eq!(&sheaf.core_chart().expect("the sheaf's base chart"), &chart);
    for k in 0..2 {
        assert_eq!(
            sheaf.coboundary(k as u32).expect("the sheaf coboundary"),
            core.coboundary(k).unwrap().expect("d_k"),
            "the rank-one sheaf coboundary is the core d"
        );
    }

    let held = BoundaryCondition::VanishingOn {
        lineage: "the last occurrence is held at zero".to_owned(),
        cells: BTreeSet::from([founded.vertices[3]]),
    };
    let relative = operator_of(&founded, &metric, &held);
    let relative_chart = relative.core_chart().expect("the relative chart");
    assert_eq!(relative_chart.cells(0).len(), 3);
    for grade in 0..=2_u32 {
        assert_eq!(
            relative_chart.complex().betti(grade as usize).unwrap(),
            hodge_reading(&relative, grade).unwrap().betti
        );
    }
}
