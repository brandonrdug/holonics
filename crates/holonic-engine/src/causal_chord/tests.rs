//! The causal chord's own checks.
//!
//! Every law is checked on synthetic exact material that needs no fixture and runs everywhere. The
//! last two tests are the measured M5 readings: they **refuse** rather than pass when the
//! authenticated release is absent, and the synthetic elastic-network test above them checks the
//! same construction with no fixture at all.
//!
//! Each Lean theorem of
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/CausalChord.lean` appears here by
//! name in the test that is its executable equivalent.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::inertia::inertia;
use crate::physical_constraint_grading::EdgeProvenance;
use crate::physical_constraint_complex::{ConstraintEdge, ConstraintVertexId};
use crate::rigidity_receiver::{ExactConfiguration, RigidityJacobian, rigidity_reading};

// ---------------------------------------------------------------------------------------------
// synthetic material
// ---------------------------------------------------------------------------------------------

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
    ExactRatMatrix::new(
        rows.iter()
            .map(|row| row.iter().copied().map(integer).collect())
            .collect(),
    )
    .expect("a declared integer matrix is rectangular")
}

/// Ascending coefficients, as the polynomial owner stores them.
fn polynomial(ascending: &[i64]) -> RationalPolynomial {
    RationalPolynomial::new(ascending.iter().copied().map(integer).collect())
}

fn column(entries: &[i64]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        entries.len(),
        1,
        entries.iter().map(|value| vec![integer(*value)]).collect(),
    )
    .expect("a column is rectangular")
}

fn row(entries: &[i64]) -> ExactRatMatrix {
    ExactRatMatrix::shaped(
        1,
        entries.len(),
        vec![entries.iter().copied().map(integer).collect()],
    )
    .expect("a row is rectangular")
}

fn declared(lineage: &str, state: &[&[i64]], excite: &[i64], read: &[i64]) -> Linearization {
    Linearization::declared(
        lineage,
        matrix(state),
        column(excite),
        row(read),
        vec!["u".to_owned()],
        vec!["y".to_owned()],
    )
    .expect("the declared linearization is well shaped")
}

// ---------------------------------------------------------------------------------------------
// the expansion
// ---------------------------------------------------------------------------------------------

/// **The recurrence agrees with the owner it is not replacing.**
///
/// `exact_linear.rs:336` already computes the characteristic polynomial by the same recurrence and
/// discards the intermediate matrices. This module keeps them, so the two are held to exact
/// agreement rather than allowed to drift.
#[test]
fn the_expansion_agrees_with_the_existing_characteristic_owner() {
    for state in [
        matrix(&[&[1, 2], &[3, 4]]),
        matrix(&[&[0, 1, 0], &[0, 0, 1], &[6, -11, 6]]),
        jordan_realification(),
        semisimple_realification(),
    ] {
        let expansion = resolvent_expansion(&state).expect("the expansion returns");
        let owner = state
            .characteristic_polynomial()
            .expect("the existing owner returns");
        assert_eq!(expansion.characteristic, owner);
        assert!(expansion.residual.is_zero());
    }
}

/// `(sI − A) adj(sI − A) = det(sI − A) I`, exactly, at several rational points.
#[test]
fn the_adjugate_expansion_satisfies_the_resolvent_identity() {
    let state = matrix(&[&[2, -1, 0], &[1, 3, 5], &[0, 4, -2]]);
    let expansion = resolvent_expansion(&state).expect("the expansion returns");
    let identity = ExactRatMatrix::identity(3).expect("identity");
    for point in [integer(0), integer(1), ratio(-7, 3), ratio(11, 5)] {
        let shifted = identity.scaled(&point).subtract(&state).expect("shift");
        let adjugate = expansion.adjugate_at(&point).expect("adjugate");
        let left = shifted.multiply(&adjugate).expect("product");
        let right = identity.scaled(&expansion.characteristic.evaluate(&point));
        assert_eq!(left, right, "at {point}");
    }
}

/// **The certificate is the whole polynomial identity, coefficient by coefficient.**
///
/// `(sI−A)·adj(sI−A) = det(sI−A)·I` is an identity between matrix polynomials of degree `n`, so
/// the certificate is its `n + 1` coefficient equations — including the closing one, which is
/// Cayley–Hamilton and is the only one the Faddeev–LeVerrier recurrence does not produce by
/// construction. The same holds for each transfer numerator, whose identity has degree `n − 1`.
#[test]
fn the_certificate_is_every_coefficient_of_the_identity_and_not_one_point() {
    for state in [
        matrix(&[&[1, 2], &[3, 4]]),
        matrix(&[&[2, -1, 0], &[1, 3, 5], &[0, 4, -2]]),
    ] {
        let extent = state.rows();
        let expansion = resolvent_expansion(&state).expect("the expansion returns");
        assert_eq!(expansion.certified_coefficients, extent + 1);
        assert!(expansion.residual.is_zero());
        // The closing coefficient is Cayley–Hamilton: `A M_n = −c_n I`.
        let identity = ExactRatMatrix::identity(extent).expect("identity");
        let closing = state
            .multiply(&expansion.adjugate[extent - 1])
            .expect("product");
        assert_eq!(
            closing,
            identity.scaled(&-expansion.characteristic.coefficient(0)),
            "the top coefficient identity is Cayley–Hamilton and the certificate checks it"
        );
    }

    let chord = declared(
        "certificate",
        &[&[0, 1, 0], &[0, 0, 1], &[-6, -11, -6]],
        &[0, 0, 1],
        &[1, 0, 0],
    );
    let transfer = transfer_function(&chord).expect("the transfer function returns");
    for entry in &transfer.entries {
        assert_eq!(entry.certified_coefficients, transfer.extent);
        assert!(entry.residual.is_zero());
    }
}

/// **One rational point does not certify a polynomial identity, and this exhibits a corruption it
/// cannot see.**
///
/// The old certificate evaluated `(sI−A)·adj(sI−A) − det(sI−A)·I` at the single point `s₀ = 3`.
/// `3I − A` is invertible here, so *any* perturbation of the adjugate that vanishes at `s₀`
/// passes that check — and `adj(s) + D·s − 3D` is one, for every `D`. The coefficientwise
/// certificate refuses it, because the perturbation moves two coefficients.
#[test]
fn a_single_rational_point_does_not_certify_the_adjugate_identity() {
    let state = matrix(&[&[1, 2], &[3, 4]]);
    let expansion = resolvent_expansion(&state).expect("the expansion returns");
    let extent = expansion.extent;
    assert_eq!(extent, 2);

    // `D` is any nonzero matrix; the perturbation is `D·s − 3D`, which is zero at `s = 3`.
    let bump = matrix(&[&[0, 1], &[0, 0]]);
    let corrupted = vec![
        expansion.adjugate[0].add(&bump).expect("sum"),
        expansion.adjugate[1]
            .subtract(&bump.scaled(&integer(3)))
            .expect("difference"),
    ];

    // The single-point check the certificate used to be: exactly zero, and blind.
    let decoy = ResolventExpansion {
        extent,
        characteristic: expansion.characteristic.clone(),
        adjugate: corrupted.clone(),
        certified_coefficients: 0,
        residual: Rat::zero(),
    };
    let point = integer(3);
    let identity = ExactRatMatrix::identity(extent).expect("identity");
    let shifted = identity.scaled(&point).subtract(&state).expect("shift");
    let at_point = shifted
        .multiply(&decoy.adjugate_at(&point).expect("adjugate"))
        .expect("product")
        .subtract(&identity.scaled(&expansion.characteristic.evaluate(&point)))
        .expect("difference");
    assert!(
        at_point.entries().iter().all(Zero::is_zero),
        "the corruption is invisible at the old single certificate point, which is the finding"
    );

    // The coefficientwise certificate sees it.
    assert_eq!(
        certify_adjugate(&state, &expansion.characteristic, &corrupted),
        Err(ChordRefusal::AdjugateCertificateFailure)
    );
    // And the honest expansion still passes it.
    assert_eq!(
        certify_adjugate(&state, &expansion.characteristic, &expansion.adjugate),
        Ok(Rat::zero())
    );
}

/// **The same blindness for a transfer numerator, and the same coefficientwise cure.**
///
/// A decoy numerator that agrees with the true one at `s₀ = 3` passes the single-point check and
/// fails the coefficientwise one, which compares every coefficient against `C M_k B` recomputed
/// with the other association.
#[test]
fn a_single_rational_point_does_not_certify_the_transfer_numerator() {
    let chord = declared(
        "numerator",
        &[&[0, 1, 0], &[0, 0, 1], &[-6, -11, -6]],
        &[0, 0, 1],
        &[1, 0, 0],
    );
    let transfer = transfer_function(&chord).expect("the transfer function returns");
    let extent = transfer.extent;
    let entry = transfer.entry(0, 0).expect("the single entry");
    let point = integer(3);

    // `s² − 6s + 9 = (s − 3)²` is zero at the old certificate point, so adding it moves two
    // coefficients and no value there.
    let decoy = entry
        .numerator
        .plus(&polynomial(&[9, -6, 1]));
    assert_eq!(
        decoy.evaluate(&point),
        entry.numerator.evaluate(&point),
        "the decoy agrees at the old single certificate point, which is the finding"
    );

    let mut parted = 0_usize;
    for index in 0..extent {
        let degree = extent - 1 - index;
        let truth = chord
            .readout
            .multiply(
                &transfer.expansion.adjugate[index]
                    .multiply(&chord.excitation)
                    .expect("product"),
            )
            .expect("product");
        assert_eq!(
            entry.numerator.coefficient(degree),
            *truth.get(0, 0).expect("entry"),
            "the honest numerator matches C M_k B at every coefficient"
        );
        if decoy.coefficient(degree) != *truth.get(0, 0).expect("entry") {
            parted += 1;
        }
    }
    assert_eq!(
        parted, 3,
        "the decoy moves all three coefficients of `(s − 3)²` and none of its value at the old \
         certificate point, so the coefficientwise check catches it three times over"
    );
}

/// The `extent²` equations the conserving-form solve poses are formed with checked arithmetic.
#[test]
fn a_state_extent_whose_square_overflows_is_refused_by_name() {
    assert_eq!(conserving_equation_count(4), Ok(16));
    assert_eq!(
        conserving_equation_count(usize::MAX),
        Err(ChordRefusal::StateExtentOverflows {
            extent: usize::MAX
        })
    );
    // And the reading itself still stands on an honest extent.
    let state = matrix(&[&[0, 1], &[-1, 0]]);
    assert!(conserving_receiver_space(&state).is_ok());
}

// ---------------------------------------------------------------------------------------------
// the chart-change law
// ---------------------------------------------------------------------------------------------

/// **Lean `rebase_denominator` / `rebase_numerator` / `rebase_transfer`.**
///
/// `(A, B, C) ↦ (T A T^{-1}, T B, C T^{-1})` leaves the whole transfer object fixed. That is what
/// makes it a chart change rather than a different system.
#[test]
fn the_transfer_function_is_invariant_under_a_chart_change() {
    let base = declared(
        "chart",
        &[&[0, 1, 0], &[0, 0, 1], &[-6, -11, -6]],
        &[0, 0, 1],
        &[1, 0, 0],
    );
    let original = transfer_function(&base).expect("the transfer returns");
    for chart in [
        matrix(&[&[1, 2, 0], &[0, 1, 3], &[0, 0, 1]]),
        matrix(&[&[0, 1, 0], &[1, 0, 0], &[2, -1, 5]]),
    ] {
        let rebased = base.rebased(&chart).expect("the chart is invertible");
        let moved = transfer_function(&rebased).expect("the transfer returns");
        assert_eq!(original.characteristic(), moved.characteristic());
        for entry in &original.entries {
            let other = moved
                .entry(entry.transport_path, entry.excitation)
                .expect("the same probe exists");
            assert_eq!(entry.numerator, other.numerator);
            assert_eq!(entry.reduced_numerator, other.reduced_numerator);
            assert_eq!(entry.reduced_denominator, other.reduced_denominator);
        }
    }
}

/// A singular chart is not a change of basis, and is refused by name — the same refusal
/// `inertia.rs:597` carries for the same reason.
#[test]
fn a_singular_chart_is_refused_rather_than_silently_collapsing_the_reading() {
    let base = declared("singular", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    let singular = matrix(&[&[1, 1], &[1, 1]]);
    assert_eq!(
        base.rebased(&singular).unwrap_err(),
        ChordRefusal::SingularChart
    );
}

// ---------------------------------------------------------------------------------------------
// cancellation
// ---------------------------------------------------------------------------------------------

/// **Lean `cancellation_is_strict`.**
///
/// `A = diag(1,2)`, `B = e₁`, `C = e₁ᵀ`. The eigenvalue `2` is neither excited nor observed, so it
/// cancels out of `H` — and the cancellation is *returned*, with the mode named structurally.
#[test]
fn an_unreachable_mode_appears_as_a_cancellation_and_is_reported() {
    let base = declared("cancelling", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    let transfer = transfer_function(&base).expect("the transfer returns");
    // det(sI − A) = (s−1)(s−2) = s² − 3s + 2.
    assert_eq!(transfer.characteristic(), &polynomial(&[2, -3, 1]));
    let entry = transfer.entry(0, 0).expect("the single probe");
    assert_eq!(entry.numerator, polynomial(&[-2, 1]));
    assert!(entry.cancels());
    assert_eq!(entry.cancelled, polynomial(&[-2, 1]));
    assert_eq!(entry.reduced_numerator, polynomial(&[1]));
    assert_eq!(entry.reduced_denominator, polynomial(&[-1, 1]));
    assert!(entry.residual.is_zero());

    // The whole atlas loses the same mode, and it is named rather than dropped.
    assert!(!transfer.atlas_is_complete());
    assert_eq!(transfer.atlas_cancellation, polynomial(&[-2, 1]));

    // Structurally: the mode at 2 is seen by no receiver and reached by no source.
    let modes = rational_mode_supports(&base).expect("the modes return");
    let hidden = modes
        .iter()
        .find(|mode| mode.eigenvalue == integer(2))
        .expect("2 is a rational eigenvalue");
    assert!(hidden.is_hidden());
    assert_eq!(hidden.support, vec![1]);
    assert!(hidden.excited_sources.is_empty());
    assert!(hidden.observed_receivers.is_empty());
    let live = modes
        .iter()
        .find(|mode| mode.eigenvalue == integer(1))
        .expect("1 is a rational eigenvalue");
    assert!(!live.is_hidden());
    assert_eq!(live.support, vec![0]);
    assert_eq!(live.excited_sources, vec![0]);
    assert_eq!(live.observed_receivers, vec![0]);
}

/// **The mode population agrees with the existing spectrum owner.**
///
/// [`rational_mode_supports`] reads its rational eigenvalues through the prime-lifting route
/// because `lattice_gauge::exact_spectrum`'s Sturm census descends from a Cauchy bound that a
/// physical network operator makes astronomically wide. On material where both routes are cheap
/// they must agree exactly, and this is what holds them to it.
#[test]
fn the_mode_population_agrees_with_the_existing_spectrum_owner() {
    for state in [
        matrix(&[&[1, 0], &[0, 2]]),
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        matrix(&[&[0, 1], &[2, 0]]),
    ] {
        let base = Linearization::single_probe("spectrum", state.clone(), 0, 0)
            .expect("declared");
        let mine = rational_mode_supports(&base).expect("the modes return");
        let owner = crate::lattice_gauge::exact_spectrum(&state).expect("the spectrum returns");
        let population = mine
            .iter()
            .map(|mode| (mode.eigenvalue.clone(), mode.algebraic_multiplicity))
            .collect::<Vec<_>>();
        assert_eq!(population, owner.rational_eigenvalues, "{state:?}");
    }
    // And a defective rational eigenvalue is reported as defective rather than as a second mode.
    let defective = Linearization::single_probe(
        "defective",
        matrix(&[&[2, 1, 0], &[0, 2, 0], &[0, 0, -3]]),
        0,
        0,
    )
    .expect("declared");
    let modes = rational_mode_supports(&defective).expect("the modes return");
    let doubled = modes
        .iter()
        .find(|mode| mode.eigenvalue == integer(2))
        .expect("2 is a rational eigenvalue");
    assert_eq!(doubled.algebraic_multiplicity, 2);
    assert_eq!(doubled.geometric_multiplicity, 1);
    assert!(doubled.is_defective());
}

/// Opening a second readout recovers the hidden mode: the cancellation is a property of the
/// declared atlas, not of the operator.
#[test]
fn a_wider_atlas_recovers_the_mode_a_narrower_one_cancelled() {
    let wide = Linearization::declared(
        "wide",
        matrix(&[&[1, 0], &[0, 2]]),
        ExactRatMatrix::shaped(2, 1, vec![vec![integer(1)], vec![integer(1)]]).expect("column"),
        ExactRatMatrix::identity(2).expect("identity"),
        vec!["u".to_owned()],
        vec!["y0".to_owned(), "y1".to_owned()],
    )
    .expect("declared");
    let transfer = transfer_function(&wide).expect("the transfer returns");
    assert!(transfer.atlas_is_complete());
    assert_eq!(transfer.atlas_cancellation, polynomial(&[1]));
}

// ---------------------------------------------------------------------------------------------
// poles and residues
// ---------------------------------------------------------------------------------------------

/// Multiplicity is an index, not a field beside one. `(s−1)²(s+3)` returns one factor at
/// multiplicity two and one at multiplicity one.
#[test]
fn the_pole_atlas_names_each_multiplicity_once() {
    // (s−1)²(s+3) = s³ + s² − 5s + 3
    let denominator = polynomial(&[3, -5, 1, 1]);
    let atlas = pole_atlas(&denominator, PoleReading::Certified).expect("the atlas returns");
    assert_eq!(atlas.accounted(), 3);
    let simple = atlas
        .factors
        .iter()
        .find(|factor| factor.multiplicity == 1)
        .expect("one simple factor");
    assert_eq!(simple.rational_poles, vec![integer(-3)]);
    let doubled = atlas
        .factors
        .iter()
        .find(|factor| factor.multiplicity == 2)
        .expect("one double factor");
    assert_eq!(doubled.rational_poles, vec![integer(1)]);
    assert_eq!(atlas.rational_poles(), vec![(integer(-3), 1), (integer(1), 2)]);
    // Sturm-certified isolating boxes are present and each contains its root.
    for factor in &atlas.factors {
        assert_eq!(factor.real_isolations.len(), factor.degree);
        for (interval, pole) in factor.real_isolations.iter().zip(&factor.rational_poles) {
            assert!(interval.lower < *pole && *pole < interval.upper);
        }
    }
    let half = atlas.half_plane.clone().expect("the certified half-plane");
    assert_eq!((half.left, half.axis, half.right), (1, 0, 2));
}

/// The residue at a simple rational pole is exact, and it is `N(a)/D'(a)`.
#[test]
fn the_residue_at_a_simple_rational_pole_is_exact() {
    // H(s) = 1/(s−1) + 1/(s−2): both residues are exactly one, and the numerator 2s−3 shares no
    // factor with the denominator, so nothing cancels.
    let base = declared(
        "simple-residues",
        &[&[1, 0], &[0, 2]],
        &[1, 1],
        &[1, 1],
    );
    let chord = causal_chord(&base).expect("the chord returns");
    assert_eq!(chord.components.len(), 2);
    let at_one = chord
        .components
        .iter()
        .find(|component| component.rational_pole == Some(integer(1)))
        .expect("a component at 1");
    let ChordResidue::Rational { laurent, order, .. } = &at_one.residue else {
        panic!("a rational pole carries a rational residue");
    };
    assert_eq!(*order, 1);
    assert_eq!(laurent, &vec![integer(1)]);
    let at_two = chord
        .components
        .iter()
        .find(|component| component.rational_pole == Some(integer(2)))
        .expect("a component at 2");
    let ChordResidue::Rational { laurent, .. } = &at_two.residue else {
        panic!("a rational pole carries a rational residue");
    };
    assert_eq!(laurent, &vec![integer(1)]);
    // Every component carries its excitation, its transport path and a zero residual.
    for component in &chord.components {
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert_eq!(component.source_name, "u");
        assert_eq!(component.receiver_name, "y");
        assert_eq!(component.lineage, "simple-residues");
        assert_eq!(component.approximation_error, ApproximationError::Exact);
        assert!(component.residual.is_zero());
    }
}

/// A double pole carries both Laurent coefficients, and they are the hand-computed ones.
#[test]
fn a_double_pole_carries_its_whole_laurent_head() {
    // 1/((s−1)²(s+3)) = 1/(4(s−1)²) − 1/(16(s−1)) + …
    let denominator = polynomial(&[3, -5, 1, 1]);
    let laurent = rational_laurent(&polynomial(&[1]), &denominator, &integer(1), 2)
        .expect("the Laurent head returns");
    assert_eq!(laurent, vec![ratio(1, 4), ratio(-1, 16)]);
}

/// **The residue at an irrational pole is an element of `Q[x]/(factor)`.**
///
/// `1/(s²−2)` has residue `1/(2√2) = √2/4` at `√2`; as an element of `Q[x]/(x²−2)` that is `x/4`,
/// which specializes correctly at *both* roots at once.
#[test]
fn the_residue_at_an_irrational_pole_lives_in_the_quotient_ring() {
    let factor = polynomial(&[-2, 0, 1]);
    let laurent = algebraic_laurent(&polynomial(&[1]), &factor, &factor, 1)
        .expect("the algebraic residue returns");
    assert_eq!(laurent.len(), 1);
    assert_eq!(
        laurent[0],
        RationalPolynomial::new(vec![Rat::zero(), ratio(1, 4)])
    );
    // And the pole is *named* by its factor, with the interval only a readout.
    let base = declared("irrational", &[&[0, 1], &[2, 0]], &[0, 1], &[1, 0]);
    let chord = causal_chord(&base).expect("the chord returns");
    assert_eq!(chord.characteristic(), &polynomial(&[-2, 0, 1]));
    let component = chord
        .components
        .first()
        .expect("one component for the whole factor");
    assert!(component.rational_pole.is_none());
    assert_eq!(component.pole_factor, polynomial(&[-2, 0, 1]));
    assert!(matches!(
        component.approximation_error,
        ApproximationError::IsolatingInterval(_)
    ));
}

// ---------------------------------------------------------------------------------------------
// the half-plane count
// ---------------------------------------------------------------------------------------------

#[test]
fn the_half_plane_count_places_a_hurwitz_polynomial_entirely_left() {
    // (s+1)(s+2)(s+3) = s³ + 6s² + 11s + 6
    let count = half_plane_count(&polynomial(&[6, 11, 6, 1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (3, 0, 0));
    assert!(count.is_hurwitz());
}

#[test]
fn the_half_plane_count_separates_left_axis_and_right() {
    // (s+1)(s−2)(s²+1) = s⁴ − s³ − s² − s − 2
    let count = half_plane_count(&polynomial(&[-2, -1, -1, -1, 1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (1, 2, 1));
    assert_eq!(count.total(), 4);
    assert!(!count.is_hurwitz());
}

/// The degenerate shapes the Cauchy index has to survive: a pure even polynomial, a pure odd one,
/// a repeated axis pair, and a repeated real pair.
#[test]
fn the_half_plane_count_survives_its_degenerate_shapes() {
    /// Ascending coefficients against the expected `(left, axis, right)` population.
    struct Shape {
        ascending: &'static [i64],
        expected: (usize, usize, usize),
    }
    let cases = [
        // s² + 1
        Shape { ascending: &[1, 0, 1], expected: (0, 2, 0) },
        // (s²+1)²
        Shape { ascending: &[1, 0, 2, 0, 1], expected: (0, 4, 0) },
        // s² − 1
        Shape { ascending: &[-1, 0, 1], expected: (1, 0, 1) },
        // s
        Shape { ascending: &[0, 1], expected: (0, 1, 0) },
        // s²
        Shape { ascending: &[0, 0, 1], expected: (0, 2, 0) },
        // s(s²+1)
        Shape { ascending: &[0, 1, 0, 1], expected: (0, 3, 0) },
    ];
    for case in cases {
        let count = half_plane_count(&polynomial(case.ascending)).expect("the count returns");
        assert_eq!(
            (count.left, count.axis, count.right),
            case.expected,
            "{:?}",
            case.ascending
        );
    }
}

/// **The symmetric route and the Routh–Hurwitz route return the same population.**
///
/// A symmetric operator has real spectrum, so its half-plane count *is* Sylvester's signature —
/// `inertia.rs:375`. Holding the two routes to agreement is what makes the connection real rather
/// than declared.
#[test]
fn the_half_plane_count_agrees_with_the_inertia_of_a_symmetric_operator() {
    for state in [
        matrix(&[&[2, 1], &[1, 2]]),
        matrix(&[&[-3, 1, 0], &[1, -2, 1], &[0, 1, -3]]),
        matrix(&[&[1, 2, 0], &[2, 1, 0], &[0, 0, 0]]),
    ] {
        let by_inertia = half_plane_from_symmetric(&state).expect("the inertia route returns");
        let characteristic = state
            .characteristic_polynomial()
            .expect("the characteristic polynomial returns");
        let by_routh = half_plane_count(&characteristic).expect("the Routh route returns");
        assert_eq!(
            (by_inertia.left, by_inertia.axis, by_inertia.right),
            (by_routh.left, by_routh.axis, by_routh.right),
            "{state:?}"
        );
    }
}

/// The refinement ceiling is a hostile-input guard on a loop that terminates as mathematics; a
/// polynomial that closes on the first try says so.
#[test]
fn the_half_plane_count_reports_the_shift_it_closed_at() {
    for ascending in [&[6, 11, 6, 1][..], &[-1, 0, 1][..], &[1, 0, 1][..]] {
        let count = half_plane_count(&polynomial(ascending)).expect("the count returns");
        let shift = count.shift_witness.clone().expect("a closing shift is reported");
        assert!(shift > Rat::zero(), "the shift is a positive rational");
        assert!(count.refinements < HALF_PLANE_REFINEMENT_CEILING);
        assert_eq!(
            count.total(),
            count.degree,
            "the closing condition is left + axis + right = degree"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// the non-normal case: the resolvent, not the spectrum
// ---------------------------------------------------------------------------------------------

/// **Lean `jordan_eigenvalue_eq_I`.** Both realifications have characteristic polynomial `(s²+1)²`
/// and their whole spectrum on the imaginary axis. Only one of them is semisimple.
#[test]
fn the_two_realifications_are_isospectral_and_only_one_is_semisimple() {
    let squared = polynomial(&[1, 0, 2, 0, 1]);
    for state in [jordan_realification(), semisimple_realification()] {
        assert_eq!(
            state
                .characteristic_polynomial()
                .expect("characteristic polynomial"),
            squared
        );
        let count = half_plane_count(&squared).expect("the count returns");
        assert_eq!((count.left, count.axis, count.right), (0, 4, 0));
    }
    assert!(!is_semisimple(&jordan_realification()).expect("semisimplicity decides"));
    assert!(is_semisimple(&semisimple_realification()).expect("semisimplicity decides"));
    assert_eq!(
        jordan_realification()
            .minimal_polynomial()
            .expect("minimal polynomial"),
        polynomial(&[1, 0, 2, 0, 1])
    );
    assert_eq!(
        semisimple_realification()
            .minimal_polynomial()
            .expect("minimal polynomial"),
        polynomial(&[1, 0, 1])
    );
}

/// **Lean `jordan_has_no_conserving_receiver`, executably and completely.**
///
/// The whole solution space of `AᵀG + GA = 0` is solved exactly; for the Jordan realification two
/// diagonal coordinates vanish on *every* solution, and a positive definite form has every diagonal
/// entry strictly positive. That refutes the existence of a conserving receiver for the entire
/// space, not for a sampled candidate. The semisimple realification exhibits one.
#[test]
fn the_defective_generator_admits_no_conserving_receiver_and_the_semisimple_one_does() {
    let defective =
        conserving_receiver_space(&jordan_realification()).expect("the space returns");
    assert_eq!(defective.vanishing_diagonals, vec![0, 2]);
    assert!(defective.witness.is_none());
    assert_eq!(defective.admits_positive_definite_metric(), Some(false));
    for form in &defective.basis {
        let check = rate_form(&jordan_realification(), form).expect("the rate form returns");
        for row in 0..4 {
            for column in 0..4 {
                assert!(check.at(row, column).is_zero());
            }
        }
    }

    let semisimple =
        conserving_receiver_space(&semisimple_realification()).expect("the space returns");
    assert!(semisimple.vanishing_diagonals.is_empty());
    let witness = semisimple.witness.clone().expect("a positive definite metric");
    assert!(inertia(&witness).is_positive_definite());
    assert_eq!(semisimple.admits_positive_definite_metric(), Some(true));
    let check = rate_form(&semisimple_realification(), &witness).expect("the rate form returns");
    for row in 0..4 {
        for column in 0..4 {
            assert!(check.at(row, column).is_zero());
        }
    }
}

/// **The whole point of R1's non-normal clause, as an exact inequality.**
///
/// Two operators with the *same* spectrum, both entirely on the imaginary axis. Probed at
/// `s = i + δ`, the defective resolvent's squared Frobenius norm grows like `δ^{-4}` and the
/// semisimple one's like `δ^{-2}`. Dividing `δ` by ten therefore multiplies the first reading by
/// about `10⁴` and the second by about `10²`, and `10³` separates them exactly.
#[test]
fn the_jordan_resolvent_grows_two_orders_faster_than_the_semisimple_one_at_the_same_spectrum() {
    let defective = Linearization::single_probe("jordan", jordan_realification(), 0, 0)
        .expect("the probe is declared");
    let semisimple = Linearization::single_probe("semisimple", semisimple_realification(), 0, 0)
        .expect("the probe is declared");
    let thousand = integer(1000);
    let mut defective_readings = Vec::new();
    let mut semisimple_readings = Vec::new();
    for offset in [ratio(1, 10), ratio(1, 100), ratio(1, 1000)] {
        let point = ProbePoint::new(offset.clone(), Rat::one());
        let one = resolvent_probe(&defective, &point).expect("the exact resolvent returns");
        let two = resolvent_probe(&semisimple, &point).expect("the exact resolvent returns");
        assert!(one.residual.is_zero());
        assert!(two.residual.is_zero());
        defective_readings.push(one.resolvent_frobenius_squared);
        semisimple_readings.push(two.resolvent_frobenius_squared);
    }
    for step in 0..2 {
        assert!(
            defective_readings[step + 1] > &defective_readings[step] * &thousand,
            "the defective resolvent must grow faster than 10³ per decade: {:?}",
            defective_readings
        );
        assert!(
            semisimple_readings[step + 1] < &semisimple_readings[step] * &thousand,
            "the semisimple resolvent must grow slower than 10³ per decade: {:?}",
            semisimple_readings
        );
    }
}

/// The same separation read off the transfer object rather than the resolvent: some declared probe
/// of the defective operator carries a double pole, and no probe of the semisimple one can.
#[test]
fn only_the_defective_operator_admits_a_declared_probe_with_a_double_pole() {
    let mut defective_degrees = Vec::new();
    let mut semisimple_degrees = Vec::new();
    for probe in 0..4 {
        for site in 0..4 {
            let one = Linearization::single_probe("jordan", jordan_realification(), probe, site)
                .expect("declared");
            let two =
                Linearization::single_probe("semisimple", semisimple_realification(), probe, site)
                    .expect("declared");
            defective_degrees.push(
                transfer_function(&one).expect("transfer").entries[0]
                    .reduced_denominator
                    .degree()
                    .unwrap_or(0),
            );
            semisimple_degrees.push(
                transfer_function(&two).expect("transfer").entries[0]
                    .reduced_denominator
                    .degree()
                    .unwrap_or(0),
            );
        }
    }
    assert_eq!(defective_degrees.iter().max(), Some(&4));
    assert_eq!(semisimple_degrees.iter().max(), Some(&2));
}

// ---------------------------------------------------------------------------------------------
// the rate form and the seam
// ---------------------------------------------------------------------------------------------

/// **Lean `seam_iff_gSkew`.** `LᵀG + GL − G` is exactly `rate_form(L − I/2, G)`.
#[test]
fn the_seam_form_is_the_rate_form_of_the_centred_generator() {
    let generator = matrix(&[&[1, 2, 0], &[-3, 0, 1], &[0, 5, -2]]);
    let metric = SymmetricForm::from_integers(&[vec![2, 1, 0], vec![1, 3, 1], vec![0, 1, 4]])
        .expect("a symmetric metric");
    let identity = ExactRatMatrix::identity(3).expect("identity");
    let centred = generator
        .subtract(&identity.scaled(&ratio(1, 2)))
        .expect("centring");
    assert_eq!(
        seam_form(&generator, &metric).expect("the seam form"),
        rate_form(&centred, &metric).expect("the rate form")
    );
}

/// **Lean `rateForm_congruence`.** The rate form transports by congruence, through the owner that
/// already refuses a singular chart.
#[test]
fn the_rate_form_transports_by_congruence_through_the_existing_owner() {
    let state = matrix(&[&[0, 1], &[-2, -3]]);
    let metric = SymmetricForm::from_integers(&[vec![3, 1], vec![1, 2]]).expect("a metric");
    let chart = matrix(&[&[1, 2], &[0, 1]]);
    let (direct, transported) =
        rate_form_congruence(&state, &metric, &chart).expect("the congruence returns");
    assert_eq!(direct, transported);
    // And the signature is what survives the chart change — Sylvester, at `inertia.rs:375`.
    assert_eq!(
        inertia(&rate_form(&state, &metric).expect("rate form")).signature(),
        inertia(&direct).signature()
    );
}

/// **Lean `gSkew_eigenvalue_re_eq_zero` and `seam_eigenvalue_re_eq_half`.**
///
/// A `G`-skew generator with positive definite `G` has its whole spectrum on the imaginary axis,
/// and its centred companion `L = A + I/2` has every eigenvalue at real part one half. The metric
/// here is not the identity: `A = S^{-1} K S` with `K` skew and `G = SᵀS`.
#[test]
fn a_g_skew_generator_sits_on_the_axis_and_its_centred_companion_sits_on_the_seam() {
    let skew = matrix(&[&[0, 2, -1], &[-2, 0, 3], &[1, -3, 0]]);
    let chart = matrix(&[&[1, 1, 0], &[0, 1, 2], &[0, 0, 1]]);
    let inverse = chart.inverse().expect("the chart is invertible");
    let state = inverse.multiply(&skew).expect("conjugate").multiply(&chart).expect("conjugate");
    let metric = SymmetricForm::from_rows(
        chart
            .transpose()
            .expect("transpose")
            .multiply(&chart)
            .expect("gram")
            .to_rows(),
    )
    .expect("a symmetric metric");
    assert!(inertia(&metric).is_positive_definite());
    let form = rate_form(&state, &metric).expect("the rate form returns");
    for row in 0..3 {
        for column in 0..3 {
            assert!(form.at(row, column).is_zero(), "Σ_G must vanish");
        }
    }
    let characteristic = state
        .characteristic_polynomial()
        .expect("characteristic polynomial");
    let count = half_plane_count(&characteristic).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (0, 3, 0));

    // The seam: L = A + I/2 has every eigenvalue at real part one half, which is the same statement
    // shifted — p_L(s + 1/2) has its whole root population on the axis.
    let centred = state
        .add(&ExactRatMatrix::identity(3).expect("identity").scaled(&ratio(1, 2)))
        .expect("centring");
    assert_eq!(
        seam_form(&centred, &metric).expect("the seam form"),
        SymmetricForm::zeros(3)
    );
    let shifted = centred
        .characteristic_polynomial()
        .expect("characteristic polynomial")
        .composed_with(&RationalPolynomial::new(vec![ratio(1, 2), Rat::one()]));
    let seam_count = half_plane_count(&shifted).expect("the count returns");
    assert_eq!((seam_count.left, seam_count.axis, seam_count.right), (0, 3, 0));
}

// ---------------------------------------------------------------------------------------------
// the separating atlas
// ---------------------------------------------------------------------------------------------

/// The negative graph Laplacian `A = −L` of a declared edge set on six vertices.
fn negative_laplacian(edges: &[(usize, usize)]) -> ExactRatMatrix {
    let extent = 6;
    let mut rows = vec![vec![Rat::zero(); extent]; extent];
    for (left, right) in edges {
        rows[*left][*left] = &rows[*left][*left] - Rat::one();
        rows[*right][*right] = &rows[*right][*right] - Rat::one();
        rows[*left][*right] = &rows[*left][*right] + Rat::one();
        rows[*right][*left] = &rows[*right][*left] + Rat::one();
    }
    ExactRatMatrix::shaped(extent, extent, rows).expect("a Laplacian is square")
}

/// **The governing correction, measured. Lean `spectrum_does_not_determine_response`.**
///
/// Two non-isomorphic graphs on six vertices — degree sequences `(4,2,2,2,2,2)` and `(3,3,3,2,2,1)`,
/// so they are not isomorphic by inspection — whose Laplacians have the *same* characteristic
/// polynomial. No spectral reading distinguishes them. The driving-point response at vertex `0`
/// does, exactly, and so do thirty-one other probe/readout pairs.
#[test]
fn cospectral_graphs_are_separated_by_the_response_atlas() {
    let first = negative_laplacian(&[(0, 2), (0, 3), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3)]);
    let second = negative_laplacian(&[(0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3)]);
    // Not isomorphic: the degree sequences differ.
    let degrees = |state: &ExactRatMatrix| {
        let mut found = (0..6)
            .map(|index| -state.get(index, index).expect("diagonal").clone())
            .collect::<Vec<_>>();
        found.sort();
        found
    };
    assert_ne!(degrees(&first), degrees(&second));

    let left = Linearization::single_probe("cospectral-a", first, 0, 0).expect("declared");
    let right = Linearization::single_probe("cospectral-b", second, 0, 0).expect("declared");
    let separation = separate_under_probe(&left, &right).expect("the atlas separates them");
    // s⁶ + 14s⁵ + 73s⁴ + 176s³ + 192s² + 72s — shared exactly.
    assert_eq!(
        separation.shared_characteristic,
        polynomial(&[0, 72, 192, 176, 73, 14, 1])
    );
    assert_eq!((separation.transport_path, separation.excitation), (0, 0));
    assert_eq!(
        separation.left_numerator,
        polynomial(&[12, 46, 62, 37, 10, 1])
    );
    assert_eq!(
        separation.right_numerator,
        polynomial(&[12, 52, 73, 43, 11, 1])
    );
    assert_ne!(separation.left_numerator, separation.right_numerator);
}

/// The full atlas — every probe against every readout — separates them at thirty-two of the
/// thirty-six pairs, and the four it does not are named rather than hidden.
#[test]
fn the_full_probe_atlas_counts_exactly_where_the_two_graphs_agree() {
    let identity = ExactRatMatrix::identity(6).expect("identity");
    let names = (0..6).map(|index| format!("site{index}")).collect::<Vec<_>>();
    let build = |lineage: &str, edges: &[(usize, usize)]| {
        Linearization::declared(
            lineage,
            negative_laplacian(edges),
            identity.clone(),
            identity.clone(),
            names.clone(),
            names.clone(),
        )
        .expect("declared")
    };
    let left = build(
        "cospectral-a",
        &[(0, 2), (0, 3), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3)],
    );
    let right = build(
        "cospectral-b",
        &[(0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3)],
    );
    let separation = separate_under_probe(&left, &right).expect("the atlas separates them");
    assert_eq!(separation.separating_probes.len(), 32);
}

/// Two systems the spectrum already separates are refused: the atlas has nothing to prove there.
#[test]
fn the_separation_refuses_systems_the_spectrum_already_tells_apart() {
    let left = declared("left", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    let right = declared("right", &[&[1, 0], &[0, 3]], &[1, 0], &[1, 0]);
    assert_eq!(
        separate_under_probe(&left, &right).unwrap_err(),
        ChordRefusal::NotIsospectral
    );
}

/// And a probe that cannot separate them says so rather than returning a first difference it did
/// not find.
#[test]
fn the_separation_refuses_when_no_declared_probe_separates() {
    let left = declared("left", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    let right = declared("right", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    assert_eq!(
        separate_under_probe(&left, &right).unwrap_err(),
        ChordRefusal::NoSeparatingProbe
    );
}

// ---------------------------------------------------------------------------------------------
// hostile input
// ---------------------------------------------------------------------------------------------

/// Every declared extent is checked against the material rather than trusted, and nothing is
/// allocated from a declaration.
#[test]
fn a_declaration_that_disagrees_with_its_material_is_refused_by_name() {
    let state = matrix(&[&[1, 0], &[0, 2]]);
    assert_eq!(
        Linearization::declared(
            "bad",
            matrix(&[&[1, 2, 3], &[4, 5, 6]]),
            column(&[1, 0]),
            row(&[1, 0]),
            vec!["u".to_owned()],
            vec!["y".to_owned()],
        )
        .unwrap_err(),
        ChordRefusal::StateNotSquare {
            rows: 2,
            columns: 3
        }
    );
    assert_eq!(
        Linearization::declared(
            "bad",
            state.clone(),
            column(&[1, 0, 0]),
            row(&[1, 0]),
            vec!["u".to_owned()],
            vec!["y".to_owned()],
        )
        .unwrap_err(),
        ChordRefusal::ExcitationShape { extent: 2, rows: 3 }
    );
    assert_eq!(
        Linearization::declared(
            "bad",
            state.clone(),
            column(&[1, 0]),
            row(&[1, 0, 0]),
            vec!["u".to_owned()],
            vec!["y".to_owned()],
        )
        .unwrap_err(),
        ChordRefusal::ReadoutShape {
            extent: 2,
            columns: 3
        }
    );
    assert_eq!(
        Linearization::declared(
            "bad",
            state.clone(),
            column(&[1, 0]),
            row(&[1, 0]),
            vec!["u".to_owned(), "phantom".to_owned()],
            vec!["y".to_owned()],
        )
        .unwrap_err(),
        ChordRefusal::SourceNameCount {
            declared: 2,
            columns: 1
        }
    );
    assert_eq!(
        Linearization::declared(
            "bad",
            state.clone(),
            column(&[1, 0]),
            row(&[1, 0]),
            vec!["u".to_owned()],
            vec![],
        )
        .unwrap_err(),
        ChordRefusal::ReceiverNameCount {
            declared: 0,
            rows: 1
        }
    );
    assert_eq!(
        Linearization::single_probe("bad", state, 0, 9).unwrap_err(),
        ChordRefusal::PortOutsideState { extent: 2, port: 9 }
    );
}

/// A probe point that is a pole is refused rather than returning an inverse that does not exist.
#[test]
fn a_probe_point_on_the_spectrum_is_refused() {
    let base = declared("pole", &[&[1, 0], &[0, 2]], &[1, 0], &[1, 0]);
    assert_eq!(
        resolvent_probe(&base, &ProbePoint::new(integer(1), Rat::zero())).unwrap_err(),
        ChordRefusal::ProbePointIsAPole
    );
    // And one strictly off it returns exactly, with a zero certificate.
    let probe = resolvent_probe(&base, &ProbePoint::new(integer(0), Rat::one()))
        .expect("an off-spectrum probe returns");
    assert!(probe.residual.is_zero());
}

/// The zero polynomial has no pole atlas and says so.
#[test]
fn the_zero_polynomial_has_no_half_plane_reading() {
    assert!(half_plane_count(&RationalPolynomial::zero()).is_err());
    assert!(pole_atlas(&RationalPolynomial::zero(), PoleReading::Named).is_err());
}

/// The reading round-trips through its serialized chart unchanged.
#[test]
fn a_chord_remounts_from_its_serialized_chart() {
    let base = declared("serialize", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let chord = causal_chord(&base).expect("the chord returns");
    let remounted: CausalChord =
        ron::from_str(&ron::to_string(&chord).expect("the chord serializes"))
            .expect("the chord remounts");
    assert_eq!(remounted, chord);
}

// ---------------------------------------------------------------------------------------------
// the wires
// ---------------------------------------------------------------------------------------------
//
// Every returned object of this module carries a certificate or an invariant, and `Deserialize`
// runs no constructor. Each test below builds a lawful value through the real constructor, checks
// that it round-trips unchanged, and then hands the wire a hand-tampered chart that the derived
// implementation used to accept and asserts the refusal **by the words of its own species**, so a
// test that passes against the unfixed file is impossible.

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

/// **A remounted linearization passes through its own constructor.** The port-name vectors are
/// exterior declarations against the matrix shapes, and the derived wire indexed straight past
/// them.
#[test]
fn a_linearization_wire_is_refused_when_it_does_not_fit_its_own_matrices() {
    let base = declared("wire", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let remounted: Linearization =
        serde_json::from_value(chart(&base)).expect("a lawful chart remounts");
    assert_eq!(remounted, base);

    let mut hostile = chart(&base);
    hostile["sources"] = serde_json::json!(["u", "v"]);
    let refusal = refusal_of::<Linearization>(hostile);
    assert!(
        refusal.contains("source names were declared"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&base);
    hostile["readout"]["columns"] = serde_json::json!(1);
    let refusal = refusal_of::<Linearization>(hostile);
    assert!(
        refusal.contains("readout has 1 columns"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted expansion re-runs the Faddeev--LeVerrier certificate.** The operator is recovered
/// from the identities the expansion carries and every coefficient equation is re-derived, so a
/// forged adjugate coefficient is refused rather than carried into `adjugate_at`.
#[test]
fn a_resolvent_expansion_wire_re_runs_its_own_adjugate_certificate() {
    let expansion =
        resolvent_expansion(&matrix(&[&[0, 1], &[-2, -3]])).expect("the expansion returns");
    let remounted: ResolventExpansion =
        serde_json::from_value(chart(&expansion)).expect("a lawful chart remounts");
    assert_eq!(remounted, expansion);

    let mut hostile = chart(&expansion);
    hostile["adjugate"][1]["entries"][0] = rational(&integer(99));
    let refusal = refusal_of::<ResolventExpansion>(hostile);
    assert!(
        refusal.contains("exact certificate"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&expansion);
    hostile["certified_coefficients"] = serde_json::json!(1);
    let refusal = refusal_of::<ResolventExpansion>(hostile);
    assert!(
        refusal.contains("certified coefficient count"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&expansion);
    hostile["residual"] = rational(&ratio(1, 1000));
    let refusal = refusal_of::<ResolventExpansion>(hostile);
    assert!(
        refusal.contains("exactly zero"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&expansion);
    hostile["extent"] = serde_json::json!(3);
    let refusal = refusal_of::<ResolventExpansion>(hostile);
    assert!(
        refusal.contains("adjugate coefficients"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted transfer chart re-derives its cancellation and its atlas.** The gcd and the least
/// common multiple are recomputed from the polynomials the chart already carries; a proper divisor
/// of the true gcd would still multiply back, so the products alone are not the check.
#[test]
fn a_transfer_wire_re_derives_its_cancellation_and_its_atlas() {
    let base = declared("wire", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let transfer = transfer_function(&base).expect("the transfer returns");
    let remounted: TransferFunction =
        serde_json::from_value(chart(&transfer)).expect("a lawful chart remounts");
    assert_eq!(remounted, transfer);

    let mut hostile = chart(&transfer);
    hostile["entries"][0]["numerator"]["coefficients"][0] = rational(&integer(5));
    let refusal = refusal_of::<TransferFunction>(hostile);
    assert!(
        refusal.contains("reduced factor times the cancellation")
            || refusal.contains("cancelled gcd"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&transfer);
    hostile["entries"][0]["certified_coefficients"] = serde_json::json!(1);
    let refusal = refusal_of::<TransferFunction>(hostile);
    assert!(
        refusal.contains("certified coefficient count"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&transfer);
    hostile["atlas_denominator"]["coefficients"][0] = rational(&integer(7));
    let refusal = refusal_of::<TransferFunction>(hostile);
    assert!(
        refusal.contains("lcm of the reduced entry denominators"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&transfer);
    hostile["extent"] = serde_json::json!(3);
    let refusal = refusal_of::<TransferFunction>(hostile);
    assert!(
        refusal.contains("declared extent against the expansion"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted pole chart tests its declared poles against the factor that names them.** One
/// exact evaluation per rational pole, and the factors are re-multiplied at their multiplicities
/// against the denominator they decompose.
#[test]
fn a_pole_wire_tests_its_declared_poles_against_the_factor_that_names_them() {
    // `(s+1)(s+2)²`
    let atlas = pole_atlas(&polynomial(&[4, 8, 5, 1]), PoleReading::Certified)
        .expect("the atlas returns");
    let remounted: PoleAtlas =
        serde_json::from_value(chart(&atlas)).expect("a lawful chart remounts");
    assert_eq!(remounted, atlas);

    let mut hostile = chart(&atlas);
    hostile["factors"][0]["rational_poles"][0] = rational(&integer(7));
    let refusal = refusal_of::<PoleAtlas>(hostile);
    assert!(
        refusal.contains("evaluated on the factor it names"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&atlas);
    hostile["factors"][1]["multiplicity"] = serde_json::json!(3);
    let refusal = refusal_of::<PoleAtlas>(hostile);
    assert!(
        refusal.contains("the factors account for"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&atlas);
    hostile["reading"] = serde_json::json!("named");
    let refusal = refusal_of::<PoleAtlas>(hostile);
    assert!(
        refusal.contains("present exactly under the certified reading"),
        "the refusal names the disagreement: {refusal}"
    );

    // A half-plane population that still totals the degree — so the count is lawful on its own
    // terms — but is not the one its own factors add up to.
    let mut hostile = chart(&atlas);
    hostile["half_plane"]["left"] = serde_json::json!(2);
    hostile["half_plane"]["right"] = serde_json::json!(1);
    let refusal = refusal_of::<PoleAtlas>(hostile);
    assert!(
        refusal.contains("summed with multiplicity"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted mode support re-derives its support from its own eigenvectors.** The support is a
/// property of the exhibited subspace, and `ModeSupport::is_hidden` is read off the port lists
/// beside it.
#[test]
fn a_mode_support_wire_re_derives_its_support_from_its_eigenvectors() {
    let base = declared("modes", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let supports = rational_mode_supports(&base).expect("the supports return");
    let first = supports.first().cloned().expect("a rational mode");
    let remounted: ModeSupport =
        serde_json::from_value(chart(&first)).expect("a lawful chart remounts");
    assert_eq!(remounted, first);

    let mut hostile = chart(&first);
    hostile["support"] = serde_json::json!([0]);
    let refusal = refusal_of::<ModeSupport>(hostile);
    assert!(
        refusal.contains("carried support against the exhibited eigenvectors"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&first);
    hostile["geometric_multiplicity"] = serde_json::json!(2);
    let refusal = refusal_of::<ModeSupport>(hostile);
    assert!(
        refusal.contains("exhibited eigenvector count"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted probe re-sums its own squared Frobenius norm.** That reading is the one the
/// module head says governs a non-normal response, so it is re-derived from the entries beside it.
#[test]
fn a_resolvent_probe_wire_re_sums_its_own_frobenius_norm() {
    let base = declared("probe", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let probe = resolvent_probe(&base, &ProbePoint::new(integer(0), Rat::one()))
        .expect("an off-spectrum probe returns");
    let remounted: ResolventProbe =
        serde_json::from_value(chart(&probe)).expect("a lawful chart remounts");
    assert_eq!(remounted, probe);

    let mut hostile = chart(&probe);
    hostile["resolvent_frobenius_squared"] = rational(&integer(0));
    let refusal = refusal_of::<ResolventProbe>(hostile);
    assert!(
        refusal.contains("squared Frobenius norm"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&probe);
    hostile["residual"] = rational(&ratio(1, 7));
    let refusal = refusal_of::<ResolventProbe>(hostile);
    assert!(
        refusal.contains("exactly zero"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted conserving space re-derives its refutation and re-certifies its witness.** The
/// Lean theorem `jordan_has_no_conserving_receiver` is the claim a forged witness would overturn,
/// so the witness is both re-read through Sylvester's signature and re-solved for membership.
#[test]
fn a_conserving_receiver_space_wire_re_certifies_its_witness() {
    let defective = conserving_receiver_space(&jordan_realification()).expect("the space returns");
    let remounted: ConservingReceiverSpace =
        serde_json::from_value(chart(&defective)).expect("a lawful chart remounts");
    assert_eq!(remounted, defective);

    // Positive definite, and outside the subspace: exactly the forgery the Lean theorem forbids.
    let euclidean =
        SymmetricForm::from_rows(ExactRatMatrix::identity(4).expect("identity").to_rows())
            .expect("a symmetric form");
    let mut hostile = chart(&defective);
    hostile["witness"] = chart(&euclidean);
    let refusal = refusal_of::<ConservingReceiverSpace>(hostile);
    assert!(
        refusal.contains("span of the solved basis"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&defective);
    hostile["vanishing_diagonals"] = serde_json::json!([1]);
    let refusal = refusal_of::<ConservingReceiverSpace>(hostile);
    assert!(
        refusal.contains("vanishing diagonals against the exhibited basis"),
        "the refusal names the disagreement: {refusal}"
    );

    let semisimple =
        conserving_receiver_space(&semisimple_realification()).expect("the space returns");
    let remounted: ConservingReceiverSpace =
        serde_json::from_value(chart(&semisimple)).expect("a lawful chart remounts");
    assert_eq!(remounted, semisimple);
}

/// **A remounted chord holds its components to the entries they came from.** The pole is named
/// three times over — in the factor, beside the residue and inside it — and the wire refuses a
/// chart where those three disagree.
#[test]
fn a_chord_wire_holds_its_components_to_the_entries_they_came_from() {
    let base = declared("serialize", &[&[0, 1], &[-2, -3]], &[0, 1], &[1, 0]);
    let chord = causal_chord(&base).expect("the chord returns");
    let remounted: CausalChord =
        serde_json::from_value(chart(&chord)).expect("a lawful chart remounts");
    assert_eq!(remounted, chord);

    let mut hostile = chart(&chord);
    hostile["hidden_modes"]["coefficients"] =
        serde_json::Value::Array(vec![rational(&integer(2))]);
    let refusal = refusal_of::<CausalChord>(hostile);
    assert!(
        refusal.contains("hidden modes"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&chord);
    hostile["components"][0]["rational_pole"] = rational(&integer(5));
    let refusal = refusal_of::<CausalChord>(hostile);
    assert!(
        refusal.contains("named once beside the residue") || refusal.contains("`x − pole`"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&chord);
    hostile["components"][0]["residue"]["rational"]["order"] = serde_json::json!(2);
    let refusal = refusal_of::<CausalChord>(hostile);
    assert!(
        refusal.contains("declared pole order"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&chord);
    hostile["components"][0]["approximation_error"] = serde_json::json!("factor-only");
    let refusal = refusal_of::<CausalChord>(hostile);
    assert!(
        refusal.contains("exact on exactly the rational poles"),
        "the refusal names the disagreement: {refusal}"
    );
}

/// **A remounted separation must still separate.** A chart whose two numerators agree is not a
/// separation, and the probe it names is the first of the probes it lists.
#[test]
fn an_atlas_separation_wire_must_still_separate() {
    let first = negative_laplacian(&[(0, 2), (0, 3), (0, 4), (0, 5), (1, 4), (1, 5), (2, 3)]);
    let second = negative_laplacian(&[(0, 2), (0, 4), (0, 5), (1, 2), (1, 4), (1, 5), (2, 3)]);
    let left = Linearization::single_probe("cospectral-a", first, 0, 0).expect("declared");
    let right = Linearization::single_probe("cospectral-b", second, 0, 0).expect("declared");
    let separation = separate_under_probe(&left, &right).expect("the atlas separates them");
    let remounted: AtlasSeparation =
        serde_json::from_value(chart(&separation)).expect("a lawful chart remounts");
    assert_eq!(remounted, separation);

    let mut hostile = chart(&separation);
    hostile["right_numerator"] = chart(&separation.left_numerator);
    let refusal = refusal_of::<AtlasSeparation>(hostile);
    assert!(
        refusal.contains("no declared probe separates"),
        "the refusal names the disagreement: {refusal}"
    );

    let mut hostile = chart(&separation);
    hostile["transport_path"] = serde_json::json!(1);
    let refusal = refusal_of::<AtlasSeparation>(hostile);
    assert!(
        refusal.contains("first of the declared separating probes"),
        "the refusal names the disagreement: {refusal}"
    );
}

// ---------------------------------------------------------------------------------------------
// the elastic network, synthetically
// ---------------------------------------------------------------------------------------------

fn place(coordinates: &[i64]) -> Vec<Rat> {
    coordinates.iter().copied().map(integer).collect()
}

fn triangle_jacobian() -> RigidityJacobian {
    let configuration = ExactConfiguration::declared(
        2,
        [
            (ConstraintVertexId(1), place(&[0, 0])),
            (ConstraintVertexId(2), place(&[4, 0])),
            (ConstraintVertexId(3), place(&[0, 3])),
        ],
    )
    .expect("a declared configuration");
    let mut constraints = BTreeMap::new();
    for (left, right) in [(1, 2), (1, 3), (2, 3)] {
        let (edge, _) = ConstraintEdge::new(
            ConstraintVertexId(left),
            ConstraintVertexId(right),
        )
        .expect("a well-formed edge");
        constraints.insert(edge, EdgeProvenance::Polygonal);
    }
    RigidityJacobian::found("synthetic-triangle", &configuration, &constraints)
        .expect("the Jacobian returns")
}

/// **The construction the M5 reading uses, with no fixture at all.**
///
/// `A = −JᵀJ` on a rigid planar triangle. Its kernel is exactly `ker J` — the infinitesimal motions
/// the rigidity receiver already returns — so the axis count of the chord's spectrum and `dim ker J`
/// are the same number computed two ways, and the operator is negative semidefinite with no
/// right-half-plane mode at all.
#[test]
fn the_elastic_network_of_a_rigid_triangle_has_its_motions_on_the_axis() {
    let jacobian = triangle_jacobian();
    let reading = rigidity_reading(&jacobian).expect("the rigidity reading returns");
    let network = elastic_network(
        "synthetic-triangle",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        4,
    )
    .expect("the network returns");
    let count = half_plane_from_symmetric(&network.state).expect("the inertia route returns");
    assert_eq!(count.right, 0, "−JᵀJ is negative semidefinite");
    assert_eq!(
        count.axis, reading.motion_dimension,
        "the axis modes are exactly the infinitesimal motions"
    );
    assert_eq!(count.left + count.axis, 6);

    let chord = causal_chord_read(&network, PoleReading::Named).expect("the chord returns");
    assert_eq!(chord.extent, 6);
    assert!(chord.semisimple, "a symmetric operator is semisimple");
    // Every returned component carries its whole provenance.
    for component in &chord.components {
        assert_eq!(component.lineage, "synthetic-triangle");
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert!(component.residual.is_zero());
    }
    // The transfer entry's certificate is exactly zero and the reduced denominator divides the
    // characteristic polynomial.
    let entry = &chord.transfer.entries[0];
    assert!(entry.residual.is_zero());
    assert!(
        entry
            .denominator
            .divided_exactly_by(&entry.reduced_denominator)
            .is_ok()
    );
}

// ---------------------------------------------------------------------------------------------
// the measured M5 presentation
// ---------------------------------------------------------------------------------------------

const STRUCTURE_ROOT_ENV: &str = "HOLONICS_M5_STRUCTURE_ROOT";
const DEFAULT_STRUCTURE_ROOT: &str = "/home/b/Downloads/holonics-m5-rbx1-rank05";
/// The RBX1 chain is the one component present in all three presentations.
const RBX1_RESIDUES: usize = 108;
/// The residue window the chord is measured on. The exact transfer object of a `3·n × 3·n` operator
/// is a `3n`-step Faddeev–LeVerrier recurrence over exact rationals; the window is **declared here**
/// rather than inferred, and it is smaller than the rigidity receiver's twenty-four because this
/// receiver computes a characteristic polynomial and that one computes a rank.
const WINDOW: usize = 5;
/// Eight angstroms, squared, on the exact decimal wire the intake reads.
const CONTACT_SQUARED: i64 = 64;

/// One alpha carbon, exactly: the deposited decimal is a rational and is used as one.
fn exact_decimal(token: &str) -> Result<Rat, String> {
    let token = token
        .strip_prefix('\'')
        .and_then(|body| body.strip_suffix('\''))
        .unwrap_or(token);
    let negative = token.starts_with('-');
    let unsigned = token.trim_start_matches(['-', '+']);
    let (whole, fraction) = unsigned.split_once('.').unwrap_or((unsigned, ""));
    if whole.is_empty()
        || !whole.chars().all(|character| character.is_ascii_digit())
        || !fraction.chars().all(|character| character.is_ascii_digit())
    {
        return Err(format!("coordinate token {token:?} is not a plain decimal"));
    }
    let digits = format!("{whole}{fraction}");
    let numerator = digits
        .parse::<BigInt>()
        .map_err(|error| error.to_string())?;
    let denominator = BigInt::from(10_u8).pow(fraction.len() as u32);
    let value = Rat::new(numerator, denominator);
    Ok(if negative { -value } else { value })
}

/// The alpha carbons of every chain, in residue order, as exact rational places.
fn read_alpha_carbons(path: &Path) -> Result<BTreeMap<String, Vec<Vec<Rat>>>, String> {
    let text = std::fs::read_to_string(path).map_err(|error| error.to_string())?;
    let lines = text.lines().collect::<Vec<_>>();
    let mut headers = Vec::<String>::new();
    let mut rows = Vec::<Vec<&str>>::new();
    let mut at = 0usize;
    while at < lines.len() {
        if lines[at].trim() != "loop_" {
            at += 1;
            continue;
        }
        let mut cursor = at + 1;
        let mut candidate = Vec::<String>::new();
        while cursor < lines.len() && lines[cursor].trim_start().starts_with('_') {
            candidate.push(lines[cursor].trim().to_owned());
            cursor += 1;
        }
        if !candidate.iter().any(|name| name.starts_with("_atom_site.")) {
            at = cursor;
            continue;
        }
        headers = candidate;
        while cursor < lines.len() {
            let line = lines[cursor].trim();
            if line == "#" || line == "loop_" || line.starts_with('_') {
                break;
            }
            if !line.is_empty() {
                let fields = line.split_whitespace().collect::<Vec<_>>();
                if fields.len() != headers.len() {
                    return Err(format!(
                        "{} atom_site row {} has {} fields under {} headers",
                        path.display(),
                        cursor + 1,
                        fields.len(),
                        headers.len()
                    ));
                }
                rows.push(fields);
            }
            cursor += 1;
        }
        break;
    }
    if headers.is_empty() || rows.is_empty() {
        return Err(format!("{} has no atom_site loop", path.display()));
    }
    let column_of = |name: &str| -> Result<usize, String> {
        headers
            .iter()
            .position(|candidate| candidate == name)
            .ok_or_else(|| format!("{} has no {name} atom_site face", path.display()))
    };
    let atom = column_of("_atom_site.label_atom_id")?;
    let chain = column_of("_atom_site.label_asym_id")?;
    let x = column_of("_atom_site.Cartn_x")?;
    let y = column_of("_atom_site.Cartn_y")?;
    let z = column_of("_atom_site.Cartn_z")?;

    let mut chains: BTreeMap<String, Vec<Vec<Rat>>> = BTreeMap::new();
    for entry in rows {
        if entry[atom] != "CA" {
            continue;
        }
        let mut point = Vec::with_capacity(3);
        for axis in [x, y, z] {
            point.push(exact_decimal(entry[axis])?);
        }
        chains.entry(entry[chain].to_owned()).or_default().push(point);
    }
    Ok(chains)
}

fn squared_distance(left: &[Rat], right: &[Rat]) -> Rat {
    left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    })
}

/// The rigidity Jacobian of one declared residue window of one M5 presentation.
fn measured_jacobian(lineage: &'static str, path: &Path) -> Result<RigidityJacobian, String> {
    let chains = read_alpha_carbons(path)?;
    let rbx1 = chains
        .values()
        .filter(|places| places.len() == RBX1_RESIDUES)
        .collect::<Vec<_>>();
    if rbx1.len() != 1 {
        return Err(format!(
            "{} carries {} chains of {RBX1_RESIDUES} alpha carbons, not one",
            path.display(),
            rbx1.len()
        ));
    }
    let window = &rbx1[0][..WINDOW];
    let configuration = ExactConfiguration::declared(
        3,
        window
            .iter()
            .enumerate()
            .map(|(at, point)| (ConstraintVertexId(at as u64 + 1), point.clone())),
    )
    .map_err(|error| error.to_string())?;
    let aperture = Rat::from_integer(BigInt::from(CONTACT_SQUARED));
    let mut constraints = BTreeMap::new();
    for left in 0..WINDOW {
        for right in (left + 1)..WINDOW {
            let backbone = right == left + 1;
            if !backbone && squared_distance(&window[left], &window[right]) > aperture {
                continue;
            }
            let (edge, _) = ConstraintEdge::new(
                ConstraintVertexId(left as u64 + 1),
                ConstraintVertexId(right as u64 + 1),
            )
            .map_err(|error| error.to_string())?;
            constraints.insert(
                edge,
                if backbone {
                    EdgeProvenance::Polygonal
                } else {
                    EdgeProvenance::AdmittedContact
                },
            );
        }
    }
    RigidityJacobian::found(lineage, &configuration, &constraints)
        .map_err(|error| error.to_string())
}

/// **The measured causal chord of one authenticated M5 presentation.**
///
/// The object is the rigidity receiver's own exact rational Jacobian on a declared five-residue
/// window of the RBX1 chain. The declared elastic-network form is `A = −JᵀJ`: the overdamped
/// relaxation of the quadratic constraint energy at unit mobility, which is symmetric negative
/// semidefinite with `ker A = ker J`. The declared probe site is the first coordinate of the first
/// residue and the declared readout site is the first coordinate of the third residue, so the chord
/// is the response transported along the chain.
///
/// The reading is [`PoleReading::Named`] and says so: the poles are named by their exact squarefree
/// factors and their multiplicities, the half-plane population comes from Sylvester's signature
/// through `inertia.rs:375` rather than from the Routh–Hurwitz route, and no isolating boxes are
/// taken. **Absent the release this test refuses.** Every law this module owns is checked without
/// any fixture by the synthetic tests above.
///
/// **`#[ignore]`d because it is a measurement, not a law.** A fifteen-coordinate exact
/// Faddeev–LeVerrier recurrence over rationals whose numerators reach a hundred and twenty digits
/// costs 38 s on the declared workstation, against under a second for every other test in this
/// module. Run it with
/// `cargo test -p holonic-engine --lib causal_chord::tests::the_causal_chord_measures -- --ignored --nocapture`.
/// Measured 2026-09-17 on `designed-free-rbx1.cif`: extent 15, 10 constraints, `rank J = 9`,
/// `dim ker J = 6`, spectrum `(left, axis, right) = (9, 6, 0)`, characteristic degree 15, atlas
/// denominator degree 10, cancelled degree 5, one pole factor, two components, residual exactly 0.
#[test]
#[ignore = "a 38 s exact measurement on the authenticated M5 release, not a law"]
fn the_causal_chord_measures_one_m5_presentation() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the measured causal chord cannot be \
         taken, and this test refuses to report success without taking it. Place the authenticated \
         release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif. Every law this module owns is checked without any fixture by the \
         synthetic tests above, in particular \
         the_elastic_network_of_a_rigid_triangle_has_its_motions_on_the_axis.",
        root.display()
    );
    let jacobian = measured_jacobian("designed-free", &root.join("designed-free-rbx1.cif"))
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let rigidity = rigidity_reading(&jacobian).expect("the rigidity reading returns");

    let probe = 0;
    let readout_site = 6;
    let network = elastic_network(
        "designed-free|rbx1|window5|-JtJ",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        probe,
        readout_site,
    )
    .expect("the network returns");
    assert_eq!(network.extent(), 3 * WINDOW);

    // The half-plane population, through the owner that already answers it exactly for a symmetric
    // form. The axis count must equal `dim ker J`, which the rigidity receiver computed
    // independently as a rank.
    let count = half_plane_from_symmetric(&network.state).expect("the inertia route returns");
    assert_eq!(count.right, 0, "−JᵀJ carries no growing mode");
    assert_eq!(
        count.axis, rigidity.motion_dimension,
        "the axis modes of −JᵀJ are exactly the infinitesimal motions of J"
    );
    assert_eq!(count.total(), 3 * WINDOW);

    let chord = causal_chord_read(&network, PoleReading::Named).expect("the chord returns");
    assert!(chord.semisimple);
    assert_eq!(chord.poles.accounted(), chord.transfer.atlas_denominator.degree().unwrap_or(0));
    let entry = &chord.transfer.entries[0];
    assert!(entry.residual.is_zero());
    assert!(
        entry.reduced_numerator.degree().unwrap_or(0)
            <= entry.reduced_denominator.degree().unwrap_or(0),
        "a strictly proper network response has no polynomial part"
    );
    for component in &chord.components {
        assert_eq!(component.excitation, 0);
        assert_eq!(component.transport_path, 0);
        assert_eq!(component.lineage, "designed-free|rbx1|window5|-JtJ");
        assert!(component.residual.is_zero());
    }

    println!(
        "causal_chord M5 | designed-free | window {WINDOW} residues | extent {} | constraints {} \
         | rank J {} | dim ker J {} | spectrum (left, axis, right) ({}, {}, {}) | \
         det degree {} | atlas denominator degree {} | cancelled degree {} | pole factors {} | \
         components {} | probe coordinate {probe} | readout coordinate {readout_site} | \
         reading Named | residual 0",
        network.extent(),
        jacobian.constraint_count(),
        rigidity.rank,
        rigidity.motion_dimension,
        count.left,
        count.axis,
        count.right,
        chord.characteristic().degree().unwrap_or(0),
        chord.transfer.atlas_denominator.degree().unwrap_or(0),
        chord.hidden_modes.degree().unwrap_or(0),
        chord.poles.factors.len(),
        chord.components.len(),
    );
}

/// **The certified reading of the same degree-fifteen M5 chord.**
///
/// [`PoleReading::Certified`] adds, to everything [`PoleReading::Named`] returns, a Sturm-certified
/// isolating box per real root of every pole factor and a sign-certified half-plane count. On this
/// object the denominator is degree ten over a characteristic polynomial of degree fifteen whose
/// coefficients reach a hundred and twenty digits, which is exactly the size at which the isolation
/// owner's cost decides whether the certified reading is affordable at all.
///
/// The reading is compared against the `Named` one on the parts both carry, so the certification
/// is held to change nothing but what it adds.
#[test]
#[ignore = "the certified degree-15 reading of the authenticated M5 chord; measured cost is printed"]
fn the_certified_chord_reads_the_same_m5_presentation() {
    let root = std::env::var_os(STRUCTURE_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_STRUCTURE_ROOT));
    assert!(
        root.is_dir(),
        "the authenticated M5 structure root {} is absent, so the certified chord cannot be \
         measured, and this test refuses to report success without measuring it. Place the \
         authenticated release at that path, or set {STRUCTURE_ROOT_ENV} to the directory carrying \
         designed-free-rbx1.cif.",
        root.display()
    );
    let jacobian = measured_jacobian("designed-free", &root.join("designed-free-rbx1.cif"))
        .unwrap_or_else(|error| panic!("designed-free: {error}"));
    let network = elastic_network(
        "designed-free|rbx1|window5|-JtJ",
        &jacobian.matrix,
        NetworkForm::OverdampedRelaxation,
        0,
        6,
    )
    .expect("the network returns");

    let started = std::time::Instant::now();
    let named = causal_chord_read(&network, PoleReading::Named).expect("the named chord returns");
    let named_elapsed = started.elapsed();

    let started = std::time::Instant::now();
    let certified =
        causal_chord_read(&network, PoleReading::Certified).expect("the certified chord returns");
    let certified_elapsed = started.elapsed();

    assert_eq!(certified.poles.factors.len(), named.poles.factors.len());
    assert_eq!(certified.poles.accounted(), named.poles.accounted());
    assert_eq!(
        certified.transfer.atlas_denominator,
        named.transfer.atlas_denominator
    );
    let count = certified
        .poles
        .half_plane
        .clone()
        .expect("the certified reading carries the half-plane count");
    assert_eq!(
        count.total(),
        certified.transfer.atlas_denominator.degree().unwrap_or(0),
        "the certified half-plane count must account for the whole atlas denominator"
    );

    // The degree-fifteen cross-check the plan asks for: Routh-Hurwitz on the characteristic
    // polynomial against Sylvester's signature on the same symmetric operator.
    let started = std::time::Instant::now();
    let by_routh =
        half_plane_count(certified.characteristic()).expect("the Routh-Hurwitz route returns");
    let routh_elapsed = started.elapsed();
    let symmetric = half_plane_from_symmetric(&network.state).expect("the symmetric route returns");
    assert_eq!(
        (by_routh.left, by_routh.axis, by_routh.right),
        (symmetric.left, symmetric.axis, symmetric.right),
        "the Routh-Hurwitz half-plane count disagrees with Sylvester's signature on the same \
         symmetric operator"
    );

    let isolations: usize = certified
        .poles
        .factors
        .iter()
        .map(|factor| factor.real_isolations.len())
        .sum();
    println!(
        "causal_chord M5 certified | designed-free | characteristic degree {} | denominator \
         degree {} | pole factors {} | real isolations {} | denominator half-plane \
         (left, axis, right) ({}, {}, {}) | characteristic half-plane ({}, {}, {}) | \
         Named {:?} | Certified {:?} | degree-15 Routh-Hurwitz {:?}",
        certified.characteristic().degree().unwrap_or(0),
        certified.transfer.atlas_denominator.degree().unwrap_or(0),
        certified.poles.factors.len(),
        isolations,
        count.left,
        count.axis,
        count.right,
        by_routh.left,
        by_routh.axis,
        by_routh.right,
        named_elapsed,
        certified_elapsed,
        routh_elapsed,
    );
}
