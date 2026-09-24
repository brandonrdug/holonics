//! The causal chord's own checks.
//!
//! Exact laws are checked on synthetic material with no external fixture.
//!
//! Each Lean theorem of
//! `Foundation/CausalChord` appears here by
//! name in the test that is its executable equivalent.

use crate::ratio::polynomial::HALF_PLANE_REFINEMENT_CEILING;
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::ratio::linear::inertia::inertia;

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
/// The exact linear carrier computes the characteristic polynomial by the same recurrence and
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
///
/// **One point is not a certificate.** An adjugate corrupted by `D·s − 3D` agrees with the true one
/// at `s = 3`, so the single-point check passes it; the coefficientwise certificate refuses it.
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

    // The corrupted half: `D` is any nonzero matrix, and the perturbation `D·s − 3D` vanishes at
    // `s = 3`.
    let state = matrix(&[&[1, 2], &[3, 4]]);
    let expansion = resolvent_expansion(&state).expect("the expansion returns");
    let extent = expansion.extent;
    let bump = matrix(&[&[0, 1], &[0, 0]]);
    let corrupted = vec![
        expansion.adjugate[0].add(&bump).expect("sum"),
        expansion.adjugate[1]
            .subtract(&bump.scaled(&integer(3)))
            .expect("difference"),
    ];
    let decoy = ResolventExpansion {
        extent,
        characteristic: expansion.characteristic.clone(),
        adjugate: corrupted.clone(),
        certified_coefficients: 0,
        residual: Rat::zero(),
    };
    let point = integer(3);
    let identity = ExactRatMatrix::identity(extent).expect("identity");
    let at_point = identity
        .scaled(&point)
        .subtract(&state)
        .expect("shift")
        .multiply(&decoy.adjugate_at(&point).expect("adjugate"))
        .expect("product")
        .subtract(&identity.scaled(&expansion.characteristic.evaluate(&point)))
        .expect("difference");
    assert!(
        at_point.entries().iter().all(Zero::is_zero),
        "the corruption is invisible at the single point"
    );
    assert_eq!(
        certify_adjugate(&state, &expansion.characteristic, &corrupted),
        Err(ChordRefusal::AdjugateCertificateFailure)
    );
    assert_eq!(
        certify_adjugate(&state, &expansion.characteristic, &expansion.adjugate),
        Ok(Rat::zero())
    );
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

/// A singular chart is not a change of basis, and is refused by name, as the inertia
/// owner's congruence refuses it.
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
    assert_eq!(
        atlas.rational_poles(),
        vec![(integer(-3), 1), (integer(1), 2)]
    );
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
    let base = declared("simple-residues", &[&[1, 0], &[0, 2]], &[1, 1], &[1, 1]);
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
        Shape {
            ascending: &[1, 0, 1],
            expected: (0, 2, 0),
        },
        // (s²+1)²
        Shape {
            ascending: &[1, 0, 2, 0, 1],
            expected: (0, 4, 0),
        },
        // s² − 1
        Shape {
            ascending: &[-1, 0, 1],
            expected: (1, 0, 1),
        },
        // s
        Shape {
            ascending: &[0, 1],
            expected: (0, 1, 0),
        },
        // s²
        Shape {
            ascending: &[0, 0, 1],
            expected: (0, 2, 0),
        },
        // s(s²+1)
        Shape {
            ascending: &[0, 1, 0, 1],
            expected: (0, 3, 0),
        },
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
/// A symmetric operator has real spectrum, so its half-plane count *is* Sylvester's signature.
/// Holding the two routes to agreement is what makes the connection real rather
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
        let shift = count
            .shift_witness
            .clone()
            .expect("a closing shift is reported");
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
    let defective = conserving_receiver_space(&jordan_realification()).expect("the space returns");
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
    let witness = semisimple
        .witness
        .clone()
        .expect("a positive definite metric");
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
    // And the signature is what survives the chart change — Sylvester.
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
    let state = inverse
        .multiply(&skew)
        .expect("conjugate")
        .multiply(&chart)
        .expect("conjugate");
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
        .add(
            &ExactRatMatrix::identity(3)
                .expect("identity")
                .scaled(&ratio(1, 2)),
        )
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
    assert_eq!(
        (seam_count.left, seam_count.axis, seam_count.right),
        (0, 3, 0)
    );
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
    let names = (0..6)
        .map(|index| format!("site{index}"))
        .collect::<Vec<_>>();
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
