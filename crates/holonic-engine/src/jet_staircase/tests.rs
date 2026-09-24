//! Tests for the jet staircase. Every value is exact over `Q`; no float decides anything and no
//! fixture is read from disk.

use num_bigint::BigInt;
use num_traits::{One, Zero};
use holonics::geometry::Rat;

use super::*;
use crate::junction_law::JointOrder;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn vector(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|value| integer(*value)).collect()
}

fn unit() -> JetChart {
    JetChart::unit("test|unit")
}

// ---------------------------------------------------------------------------------------------
// 1. the ladder restricts by forgetting the top order
// ---------------------------------------------------------------------------------------------

/// Lean: `Transport/JetStaircase.lean::truncate_idem`,
/// `Transport/JetStaircase.lean::truncate_comp`,
/// `Transport/JetStaircase.lean::truncate_fibre_is_the_top_coefficient`.
#[test]
fn the_jet_ladder_restricts_by_forgetting_the_top_order() {
    let top = FiniteJet::from_integers(unit(), &[3, -1, 4, 2]).expect("the jet stands");
    assert_eq!(top.order(), 3);
    let ladder = jet_ladder(&top).expect("the ladder stands");
    assert_eq!(ladder.top_order(), 3);
    assert!(ladder.restriction_is_projection());
    for order in 0..=3 {
        let rung = ladder.rung(order).expect("every rung is present");
        assert_eq!(rung.order(), order);
        assert_eq!(rung.coefficients(), &top.coefficients()[..=order]);
    }
    // The fibre of one restriction step is the one discarded coefficient, at every step.
    for order in 1..=3 {
        assert_eq!(ladder.restriction_fibre_dimension(order), Some(1));
    }
    assert_eq!(ladder.restriction_fibre_dimension(0), None);
    assert_eq!(ladder.restriction_fibre_dimension(4), None);

    // Restriction really forgets: two jets differing only above `r` restrict to the same rung.
    let sibling = FiniteJet::from_integers(unit(), &[3, -1, 4, 9]).expect("the jet stands");
    assert_ne!(sibling, top);
    assert_eq!(
        sibling.restrict().expect("restricts"),
        top.restrict().expect("restricts")
    );
}

#[test]
fn the_order_zero_jet_has_nothing_to_restrict_and_says_so() {
    let jet = FiniteJet::from_integers(unit(), &[7]).expect("the jet stands");
    assert!(matches!(
        jet.restrict(),
        Err(StaircaseRefusal::NothingToRestrict)
    ));
}

#[test]
fn a_chart_with_a_zero_step_and_a_jet_with_no_coefficient_are_refused_by_name() {
    assert!(matches!(
        JetChart::declare("test|degenerate", Rat::zero(), Rat::zero()),
        Err(StaircaseRefusal::ZeroStep)
    ));
    assert!(matches!(
        FiniteJet::declare(unit(), Vec::new()),
        Err(StaircaseRefusal::EmptyJet)
    ));
    let oversize = vec![Rat::zero(); JET_ORDER_CEILING + 2];
    assert!(matches!(
        FiniteJet::declare(unit(), oversize),
        Err(StaircaseRefusal::OrderBeyondCeiling { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 2. a finite jet retains several continuations, and the family is the return
// ---------------------------------------------------------------------------------------------

/// Lean: `Transport/JetStaircase.lean::truncate_eq_iff`,
/// `Transport/JetStaircase.lean::truncate_forgets_above`.
#[test]
fn a_finite_jet_retains_an_affine_family_of_continuations() {
    let jet = FiniteJet::from_integers(unit(), &[1, 2]).expect("the jet stands");
    let family = jet.compatible_polynomials(5).expect("the family stands");
    assert_eq!(family.dimension(), 4, "degree 5 above order 1 leaves four");
    assert_eq!(family.base_point()[..2], jet.coefficients()[..2]);

    // Two different members, both agreeing with the jet, and neither preferred.
    let left = family
        .member(&vector(&[1, 0, 0, 0]))
        .expect("the member stands");
    let right = family
        .member(&vector(&[0, 0, 0, -7]))
        .expect("the member stands");
    assert_ne!(left, right);
    for member in [&left, &right] {
        assert_eq!(&member.coefficients()[..2], jet.coefficients());
        assert!(family.contains(member.coefficients()));
    }
    // A vector that disagrees with the jet is not in the family.
    assert!(!family.contains(&vector(&[1, 3, 0, 0, 0, 0])));

    // The same order at the same degree is a single point: the jet is its own continuation.
    let exact = jet.compatible_polynomials(1).expect("the family stands");
    assert_eq!(exact.dimension(), 0);
}

#[test]
fn a_family_below_the_jets_own_order_and_one_past_the_ceiling_are_refused() {
    let jet = FiniteJet::from_integers(unit(), &[1, 2, 3]).expect("the jet stands");
    assert!(matches!(
        jet.compatible_polynomials(1),
        Err(StaircaseRefusal::DegreeBelowJetOrder {
            degree: 1,
            order: 2
        })
    ));
    assert!(matches!(
        jet.compatible_polynomials(FAMILY_DEGREE_CEILING + 1),
        Err(StaircaseRefusal::DegreeBeyondCeiling { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 3. difference data and jet data are one exact triangular change of basis
// ---------------------------------------------------------------------------------------------

/// Lean: `Transport/JetStaircase.lean::coefficient_eq_iteratedDelta_at_zero`,
/// `Transport/JetStaircase.lean::iteratedDelta_ofCoefficients_eq_zero`.
#[test]
fn difference_data_and_jet_data_are_one_exact_change_of_basis() {
    // A genuinely rational chart: base 1/2, step 1/3, and a cubic with rational coefficients.
    let chart = JetChart::declare("test|rational", ratio(1, 2), ratio(1, 3)).expect("the chart");
    let jet = FiniteJet::declare(
        chart.clone(),
        vec![ratio(2, 5), ratio(-3, 7), integer(4), ratio(1, 6)],
    )
    .expect("the jet stands");
    let table = DifferenceTable::sampled_from(&jet, 8).expect("the samples stand");

    // Forward: the samples reconstruct the jet exactly.
    let recovered = table.to_jet(3).expect("the change of basis returns");
    assert_eq!(recovered, jet, "Newton's formula is exact over Q");

    // Backward: the jet reproduces the differences exactly.
    let differences = jet_to_differences(&jet, 8).expect("the inverse returns");
    assert_eq!(differences, table.forward_differences());

    // A cubic is annihilated at order four and not before.
    assert_eq!(table.annihilating_order(), OrderReading::Annihilated(4));
    assert_eq!(table.annihilating_order().degree(), Some(3));
    assert!(table.difference_column(4).expect("column").iter().all(Zero::is_zero));
    assert!(!table.difference_column(3).expect("column").iter().all(Zero::is_zero));

    // And the reconstruction residual on polynomial input is exactly zero at every node.
    let residual = table.reconstruction_residual(&jet).expect("the residual");
    assert!(residual.iter().all(Zero::is_zero));
}

#[test]
fn the_reconstruction_residual_is_computed_on_input_that_is_not_polynomial() {
    // `2^n` is not polynomial, so the degree-2 truncation leaves it and the owner says where.
    let values = vector(&[1, 2, 4, 8, 16, 32]);
    let table = DifferenceTable::declare(unit(), values).expect("the samples stand");
    let jet = table.to_jet(2).expect("the truncation returns");
    let residual = table.reconstruction_residual(&jet).expect("the residual");
    assert!(
        residual[..3].iter().all(Zero::is_zero),
        "the truncation interpolates the first three nodes exactly"
    );
    assert!(
        !residual[3].is_zero(),
        "and leaves the source at the fourth: {}",
        residual[3]
    );
    // Not resolved as a polynomial at all inside this sample.
    assert_eq!(
        table.annihilating_order(),
        OrderReading::NotResolvedWithin(6)
    );
    assert_eq!(table.annihilating_order().order(), None);
}

#[test]
fn an_order_beyond_the_sample_and_a_sample_past_the_ceiling_are_refused_by_name() {
    let table = DifferenceTable::declare(unit(), vector(&[1, 2, 3])).expect("the samples stand");
    assert!(matches!(
        table.to_jet(3),
        Err(StaircaseRefusal::OrderExceedsSamples {
            order: 3,
            samples: 3,
            needed: 4
        })
    ));
    assert!(matches!(
        table.difference_column(9),
        Err(StaircaseRefusal::OrderExceedsSamples { .. })
    ));
    assert!(matches!(
        DifferenceTable::declare(unit(), Vec::new()),
        Err(StaircaseRefusal::EmptySamples)
    ));
    assert!(matches!(
        DifferenceTable::sampled_from(
            &FiniteJet::from_integers(unit(), &[1]).expect("jet"),
            SAMPLE_CEILING + 1
        ),
        Err(StaircaseRefusal::SamplesBeyondCeiling { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 4. the staircase (i): repeated integration with boundary data as an encoding
// ---------------------------------------------------------------------------------------------

/// A source with a sparse third difference: a cubic over most of its range, with one kick.
fn sparse_source() -> DifferenceTable {
    // `f(n) = n^3` sampled at twelve nodes, then one node moved: the third difference is
    // constant-6 for a cubic, so instead use a source whose third difference is genuinely sparse.
    // Take `Δ³f` to be zero everywhere except at two places and integrate it up.
    let mut column = vec![Rat::zero(); 13];
    column[2] = integer(5);
    column[9] = integer(-3);
    let mut values = column;
    // Integrate three times from declared boundary differences 1, 2, 0.
    for boundary in [Rat::zero(), integer(2), Rat::one()] {
        let mut next = Vec::with_capacity(values.len() + 1);
        let mut running = boundary;
        next.push(running.clone());
        for entry in &values {
            running = &running + entry;
            next.push(running.clone());
        }
        values = next;
    }
    DifferenceTable::declare(unit(), values).expect("the samples stand")
}

/// Lean: `Transport/JetStaircase.lean::rebuild_iteratedDelta`,
/// `Transport/JetStaircase.lean::integrate_delta`.
#[test]
fn the_sparse_encoding_reconstructs_exactly_and_reports_its_measured_cost() {
    let table = sparse_source();
    let encoding = encode_sparse_differences(&table, 3).expect("the encoding stands");
    assert_eq!(encoding.order(), 3);
    assert_eq!(encoding.boundary().len(), 3, "three constants of integration");
    assert_eq!(
        encoding.sparse().len(),
        2,
        "the third difference has exactly two nonzero entries"
    );
    assert_eq!(
        encoding.decode().expect("the decoding returns"),
        table,
        "repeated summation is exact"
    );

    let cost = encoding.cost().expect("the cost returns");
    assert_eq!(cost.raw_terms, table.len());
    assert_eq!(cost.stored_terms, 5, "three boundary values and two kicks");
    assert!(
        cost.is_cheaper(),
        "the sparse encoding stores {} bits against the raw {}",
        cost.stored_bits,
        cost.raw_bits
    );

    // The same source encoded at an order its differences are *not* sparse at costs more terms.
    let dense = encode_sparse_differences(&table, 1).expect("the encoding stands");
    assert!(
        dense.cost().expect("cost").stored_terms > cost.stored_terms,
        "the order the source is sparse at is the one that pays"
    );
}

#[test]
fn a_declared_future_receiver_factors_through_the_encoding() {
    let table = sparse_source();
    let encoding = encode_sparse_differences(&table, 3).expect("the encoding stands");
    // Three declared receivers: a single sample, a running total, and an alternating probe.
    let mut point = vec![Rat::zero(); table.len()];
    point[7] = Rat::one();
    let total = vec![Rat::one(); table.len()];
    let alternating: Vec<Rat> = (0..table.len())
        .map(|index| if index % 2 == 0 { Rat::one() } else { -Rat::one() })
        .collect();
    for functional in [point, total, alternating] {
        let receipt = encoding
            .factors_through(&functional)
            .expect("the factorisation returns");
        assert!(
            receipt.agrees,
            "the receiver's value through the encoding disagrees: {} against {}",
            receipt.raw_value, receipt.encoded_value
        );
        assert_eq!(receipt.induced.len(), table.len());
        assert!(!receipt.support.is_empty());
    }
}

#[test]
fn a_functional_of_the_wrong_length_and_an_order_past_the_sample_are_refused() {
    let table = sparse_source();
    let encoding = encode_sparse_differences(&table, 3).expect("the encoding stands");
    assert!(matches!(
        encoding.factors_through(&vector(&[1, 2, 3])),
        Err(StaircaseRefusal::FunctionalLengthMismatch { .. })
    ));
    assert!(matches!(
        encode_sparse_differences(&table, table.len()),
        Err(StaircaseRefusal::OrderExceedsSamples { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 5. the staircase (ii): the grain's effect on the order is computed, never fixed
// ---------------------------------------------------------------------------------------------

/// **No universal one-order drop**: three computed instances on two sources, and the change is a
/// different number in each. The plan forbids hard-coding one, and this is the evidence.
#[test]
fn a_grain_changes_the_apparent_difference_order_by_an_amount_that_is_computed() {
    // (a) A quadratic under either grain keeps its order.
    let quadratic = FiniteJet::from_integers(unit(), &[0, 0, 1]).expect("the jet stands");
    let square = DifferenceTable::sampled_from(&quadratic, 12).expect("the samples stand");
    assert_eq!(square.annihilating_order(), OrderReading::Annihilated(3));
    let subsampled = coarse_grain_order(&square, &GrainMap::Subsample { stride: 2 })
        .expect("the grain reading returns");
    assert_eq!(subsampled.coarse, OrderReading::Annihilated(3));
    assert_eq!(subsampled.order_change(), Some(0));
    let blocked = coarse_grain_order(&square, &GrainMap::BlockSum { block: 2 })
        .expect("the grain reading returns");
    assert_eq!(blocked.coarse, OrderReading::Annihilated(3));
    assert_eq!(blocked.order_change(), Some(0));

    // (b) The alternating sequence resolves no order at all at the fine grain, and two different
    // grains give it two *different* coarse orders. One map, two answers: there is no universal
    // drop to hard-code.
    let alternating: Vec<Rat> = (0..12)
        .map(|index| if index % 2 == 0 { Rat::one() } else { -Rat::one() })
        .collect();
    let flip = DifferenceTable::declare(unit(), alternating).expect("the samples stand");
    assert_eq!(flip.annihilating_order(), OrderReading::NotResolvedWithin(12));
    let summed = coarse_grain_order(&flip, &GrainMap::BlockSum { block: 2 })
        .expect("the grain reading returns");
    assert_eq!(
        summed.coarse,
        OrderReading::Annihilated(0),
        "consecutive pairs cancel exactly, so the coarse sequence is zero"
    );
    let kept = coarse_grain_order(&flip, &GrainMap::Subsample { stride: 2 })
        .expect("the grain reading returns");
    assert_eq!(
        kept.coarse,
        OrderReading::Annihilated(1),
        "every other sample is the constant 1"
    );
    assert_ne!(summed.coarse, kept.coarse);
    // And with an unresolved fine order the change is not reported at all.
    assert_eq!(summed.order_change(), None);
    assert_eq!(kept.order_change(), None);
}

#[test]
fn a_zero_grain_and_a_block_that_does_not_divide_are_refused_by_name() {
    let table = DifferenceTable::declare(unit(), vector(&[1, 2, 3, 4, 5])).expect("samples");
    assert!(matches!(
        coarse_grain_order(&table, &GrainMap::BlockSum { block: 0 }),
        Err(StaircaseRefusal::ZeroGrain)
    ));
    assert!(matches!(
        coarse_grain_order(&table, &GrainMap::Subsample { stride: 0 }),
        Err(StaircaseRefusal::ZeroGrain)
    ));
    assert!(matches!(
        coarse_grain_order(&table, &GrainMap::BlockSum { block: 2 }),
        Err(StaircaseRefusal::GrainDoesNotDivide {
            grain: 2,
            samples: 5
        })
    ));
}

// ---------------------------------------------------------------------------------------------
// 6. the staircase (iii): a joint is a spline knot, and its order is the lowest jump
// ---------------------------------------------------------------------------------------------

#[test]
fn a_spline_knot_carries_the_order_of_the_lowest_derivative_that_jumps() {
    let chart = unit();
    // Left piece about 0: `x²`. Right piece about the knot 1: matched in value and slope but not
    // in curvature, so the joint order is 2.
    let pieces = vec![vector(&[0, 0, 1]), vector(&[1, 2, 5])];
    let spline = PiecewisePolynomial::declare(chart.clone(), vec![Rat::one()], pieces)
        .expect("the spline stands");
    match spline.knot_reading(0).expect("the reading returns") {
        KnotReading::Jumps { order, left, right } => {
            assert_eq!(order, JointOrder(2));
            assert_eq!(left, integer(2), "the left second derivative");
            assert_eq!(right, integer(10), "the right second derivative");
        }
        other => panic!("this knot jumps in curvature: {other:?}"),
    }

    // A knot that jumps in value is order zero.
    let broken = PiecewisePolynomial::declare(
        chart.clone(),
        vec![Rat::one()],
        vec![vector(&[0, 0, 1]), vector(&[3, 2, 1])],
    )
    .expect("the spline stands");
    match broken.knot_reading(0).expect("the reading returns") {
        KnotReading::Jumps { order, .. } => assert_eq!(order, JointOrder(0)),
        other => panic!("this knot jumps in value: {other:?}"),
    }

    // A knot that jumps nowhere returns the order it was smooth through, and mints no jump.
    let smooth = PiecewisePolynomial::declare(
        chart,
        vec![Rat::one()],
        vec![vector(&[0, 0, 1]), vector(&[1, 2, 1])],
    )
    .expect("the spline stands");
    assert_eq!(
        smooth.knot_reading(0).expect("the reading returns"),
        KnotReading::SmoothThrough { order: 2 }
    );
}

#[test]
fn a_spline_with_the_wrong_piece_count_or_unsorted_knots_is_refused_by_name() {
    assert!(matches!(
        PiecewisePolynomial::declare(unit(), vec![Rat::one()], vec![vector(&[1])]),
        Err(StaircaseRefusal::PieceCountMismatch {
            knots: 1,
            needed: 2,
            declared: 1
        })
    ));
    assert!(matches!(
        PiecewisePolynomial::declare(
            unit(),
            vec![integer(2), Rat::one()],
            vec![vector(&[1]), vector(&[1]), vector(&[1])]
        ),
        Err(StaircaseRefusal::KnotsNotIncreasing { at: 1 })
    ));
    let spline =
        PiecewisePolynomial::declare(unit(), vec![Rat::one()], vec![vector(&[1]), vector(&[1])])
            .expect("the spline stands");
    assert!(matches!(
        spline.knot_reading(4),
        Err(StaircaseRefusal::NoSuchKnot {
            at: 4,
            declared: 1
        })
    ));
}

#[test]
fn the_spline_family_of_a_jet_is_returned_whole_and_its_members_match_at_the_knots() {
    let jet = FiniteJet::from_integers(unit(), &[1, 2]).expect("the jet stands");
    let knots = vec![Rat::one(), integer(2)];
    let family = compatible_splines(&jet, &knots, 3, 1).expect("the family stands");
    // Unknowns: three pieces of four coefficients. Constraints: two from the jet, and two per
    // knot. The dimension is what the exact reduction returned, and it is plural.
    assert_eq!(family.dimension(), 12 - 2 - 4);
    assert!(family.dimension() > 0, "a jet retains several splines");

    let coordinates = vec![Rat::zero(); family.dimension()];
    let member = family.member(&coordinates).expect("the member stands");
    for knot in 0..knots.len() {
        match member.knot_reading(knot).expect("the reading returns") {
            KnotReading::Jumps { order, .. } => {
                assert!(
                    order.0 > 1,
                    "the declared smoothness is C¹, so nothing below order two may jump"
                );
            }
            KnotReading::SmoothThrough { .. } => {}
        }
    }
    // A second member is a different spline that still agrees with the jet.
    let mut other = vec![Rat::zero(); family.dimension()];
    other[0] = Rat::one();
    let second = family.member(&other).expect("the member stands");
    assert_ne!(second, member);
    assert_eq!(&second.pieces()[0][..2], jet.coefficients());
}

// ---------------------------------------------------------------------------------------------
// 7. the staircase (iv): the cusp raises the difference order on the induced face
// ---------------------------------------------------------------------------------------------

/// Lean: `Millennium/HolonicInteractionExterior.lean::cuspFluxDefect_cubicZero`,
/// `cuspFluxDefect_squareNonzero`, `cuspFluxTransport_advancesOrbit`,
/// `cuspFluxOrbit_secondDifference`, `cuspFluxOrbit_thirdDifference`. Every one is recomputed here
/// over `Q` from the two integer matrices.
#[test]
fn the_cusp_raises_the_difference_order_on_the_induced_flux_face() {
    let reading = cusp_staircase(9).expect("the reading returns");
    assert!(
        reading.exterior_square_agrees,
        "the six-dimensional transport is literally Λ²M₀"
    );
    assert!(reading.fibre_defect_square_zero, "N² = 0 on the fibre");
    assert!(reading.flux_defect_cube_zero, "D³ = 0 on the flux face");
    assert!(
        reading.flux_defect_square_nonzero,
        "D² ≠ 0: the induced defect is genuinely second order"
    );

    // The staircase itself: the fibre orbit is affine in the time, the flux orbit is quadratic.
    assert_eq!(reading.fibre_order, OrderReading::Annihilated(2));
    assert_eq!(reading.flux_order, OrderReading::Annihilated(3));
    assert_eq!(
        reading.flux_order.order().unwrap() - reading.fibre_order.order().unwrap(),
        1,
        "one exterior step raises the difference order by exactly one"
    );

    // `2 e23`, and nothing else.
    assert_eq!(reading.flux_second_difference, vector(&[0, 0, 0, 0, 0, 2]));
    assert!(reading.flux_third_difference.iter().all(Zero::is_zero));

    // The displayed orbit at `n = 8`: `e01 + n e02 + n e13 + n² e23`.
    assert_eq!(reading.flux_orbit_tail, vector(&[1, 8, 0, 0, 8, 64]));
}

#[test]
fn a_cusp_reading_too_short_to_take_the_third_difference_is_refused() {
    assert!(matches!(
        cusp_staircase(3),
        Err(StaircaseRefusal::OrderExceedsSamples { needed: 4, .. })
    ));
}

#[test]
fn the_exterior_square_of_the_identity_is_the_identity() {
    // The functor is checked on a second input, so the cusp agreement is not a coincidence of one
    // matrix.
    let identity = ExactRatMatrix::identity(4).expect("the identity stands");
    assert_eq!(
        exterior_square(&identity).expect("the exterior square returns"),
        ExactRatMatrix::identity(6).expect("the identity stands")
    );
}

// ---------------------------------------------------------------------------------------------
// 8. the Mahler/Iwasawa comparison, and where it stops
// ---------------------------------------------------------------------------------------------

#[test]
fn gamma_minus_one_is_the_forward_difference_on_the_polynomial_chart() {
    let cubic = FiniteJet::from_integers(unit(), &[1, -2, 0, 3]).expect("the jet stands");
    let table = DifferenceTable::sampled_from(&cubic, 10).expect("the samples stand");
    assert!(
        gamma_minus_one_is_forward_difference(&table, 5).expect("the check returns"),
        "T = γ − 1 and Δ are the same operator on this chart"
    );
    // And the Mahler coefficients are the finite differences at zero.
    let mahler = mahler_coefficients(&table).expect("the coefficients return");
    assert_eq!(mahler, table.forward_differences());
    assert_eq!(&mahler[..4], &table.forward_differences()[..4]);
}

#[test]
fn the_mahler_chart_agrees_on_polynomials_and_stops_at_two_to_the_n() {
    let quadratic = FiniteJet::from_integers(unit(), &[5, 1, 2]).expect("the jet stands");
    let table = DifferenceTable::sampled_from(&quadratic, 8).expect("the samples stand");
    match mahler_chart_agreement(&table, 2).expect("the comparison returns") {
        MahlerScope::PolynomialAgreement { degree, mahler, jet } => {
            assert_eq!(degree, 2);
            assert_eq!(jet, quadratic.coefficients());
            // `Δ⁰ = 5`, `Δ¹ = 1 + 2 = 3`, `Δ² = 2·2 = 4`.
            assert_eq!(mahler, vector(&[5, 3, 4]));
        }
        other => panic!("a quadratic is polynomial: {other:?}"),
    }

    match mahler_stop_witness(3, 8).expect("the witness returns") {
        MahlerScope::StopsAtNonPolynomial {
            order,
            witness_node,
            source_value,
            residual,
            ..
        } => {
            assert_eq!(order, 3);
            assert_eq!(witness_node, 4, "a cubic interpolates the first four nodes");
            assert_eq!(source_value, integer(16));
            assert!(!residual.is_zero());
        }
        other => panic!("2^n is not polynomial: {other:?}"),
    }
}

/// The functor stops: `ω_n = (1+T)^{p^n} − 1` is `γ^{p^n} − 1`, not `Δ^{p^n}`. Both are computed
/// on the same sample and they disagree. A p-adic difference chart and a real time jet are not
/// identified merely because both have levels.
#[test]
fn the_iwasawa_level_filtration_is_not_the_jet_order_filtration() {
    let square = FiniteJet::from_integers(unit(), &[0, 0, 1]).expect("the jet stands");
    let table = DifferenceTable::sampled_from(&square, 10).expect("the samples stand");
    let comparison =
        omega_action_is_not_iterated_difference(&table, 2, 1).expect("the comparison returns");
    assert_eq!(comparison.degree, 2, "ω₁ at p = 2 has degree 2");
    // `ω₁(T) = 2T + T²`, so on `n²` it returns `2·Δf(0) + Δ²f(0) = 2·1 + 2 = 4`, while `Δ²f(0) = 2`.
    assert_eq!(comparison.omega_at_base, integer(4));
    assert_eq!(comparison.iterated_difference_at_base, integer(2));
    assert!(!comparison.agrees, "the two level filtrations differ");

    // At p = 3, level 1 the degree is three and the two disagree again.
    let cubic_comparison =
        omega_action_is_not_iterated_difference(&table, 3, 1).expect("the comparison returns");
    assert_eq!(cubic_comparison.degree, 3);
    assert!(!cubic_comparison.agrees);
}

#[test]
fn a_mahler_reading_outside_the_unit_chart_is_refused_by_name() {
    let chart = JetChart::declare("test|half-step", Rat::zero(), ratio(1, 2)).expect("the chart");
    let table = DifferenceTable::declare(chart, vector(&[1, 2, 4, 8])).expect("the samples stand");
    assert!(matches!(
        mahler_coefficients(&table),
        Err(StaircaseRefusal::ChartMismatch { .. })
    ));
}

#[test]
fn a_residual_taken_across_two_charts_is_refused_rather_than_rescaled() {
    let left = DifferenceTable::declare(unit(), vector(&[1, 2, 3])).expect("samples");
    let other = JetChart::declare("test|other", Rat::one(), integer(2)).expect("the chart");
    let jet = FiniteJet::from_integers(other, &[1, 1]).expect("the jet stands");
    assert!(matches!(
        left.reconstruction_residual(&jet),
        Err(StaircaseRefusal::ChartMismatch { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 9. the local-jet owner, composed rather than re-founded
// ---------------------------------------------------------------------------------------------

#[test]
fn a_finite_jet_hands_its_coefficients_to_the_existing_local_jet_owner() {
    let jet = FiniteJet::from_integers(unit(), &[1, 0, 3, 0]).expect("the jet stands");
    let local = jet.local_jet().expect("the local jet stands");
    // The local-jet owner normalizes trailing zeros; this owner keeps them, because the order is
    // a declaration about the rung and not about the leading coefficient.
    assert_eq!(local.rank(), 3);
    assert_eq!(jet.order(), 3);
    let back = FiniteJet::from_local_jet(unit(), &local).expect("the round trip stands");
    assert_eq!(back.order(), 2);
    assert_eq!(back.evaluate(&integer(2)), jet.evaluate(&integer(2)));
}

#[test]
fn the_vanishing_order_at_the_base_is_what_a_neck_station_reads() {
    // A simple zero: the lens pinhole.
    let simple = FiniteJet::from_integers(unit(), &[0, 3, 1]).expect("the jet stands");
    assert_eq!(simple.vanishing_order(), Some(1));
    // A cusp: the first two coefficients vanish.
    let cusp = FiniteJet::from_integers(unit(), &[0, 0, 0, 7]).expect("the jet stands");
    assert_eq!(cusp.vanishing_order(), Some(3));
    // Undecided at this order: every declared coefficient vanishes and the owner says `None`
    // rather than reporting the order it happened to stop at.
    let flat = FiniteJet::from_integers(unit(), &[0, 0, 0]).expect("the jet stands");
    assert_eq!(flat.vanishing_order(), None);
    // The shift is what makes `A(s) − A_min` the thing read.
    let section = FiniteJet::from_integers(unit(), &[4, 0, 2]).expect("the jet stands");
    assert_eq!(section.shifted_by(&integer(4)).vanishing_order(), Some(2));
}

#[test]
fn the_derivative_values_are_the_coefficients_times_the_factorials() {
    let jet = FiniteJet::from_integers(unit(), &[1, 2, 3, 4]).expect("the jet stands");
    assert_eq!(jet.derivative_values(), vector(&[1, 2, 6, 24]));
    assert_eq!(jet.derivative_at(0, &Rat::zero()), integer(1));
    assert_eq!(jet.derivative_at(1, &Rat::zero()), integer(2));
    assert_eq!(jet.derivative_at(2, &Rat::zero()), integer(6));
    // And away from the base, by the exact polynomial rule.
    assert_eq!(
        jet.evaluate(&integer(2)),
        integer(1 + 2 * 2 + 3 * 4 + 4 * 8)
    );
}
