use relational_geometry::{integer, rat};

use super::*;

fn polynomial(values: &[i64]) -> RationalPolynomial {
    RationalPolynomial::new(values.iter().map(|value| integer(*value)).collect())
}

#[test]
fn exact_division_refuses_rather_than_truncating() {
    let dividend = polynomial(&[1, 0, 1]);
    let divisor = polynomial(&[1, 1]);
    assert_eq!(
        dividend.divided_exactly_by(&divisor),
        Err(ExactPolynomialError::NonExactPolynomialDivision)
    );
    let square = divisor.times(&divisor);
    assert_eq!(square.divided_exactly_by(&divisor).unwrap(), divisor);
}

#[test]
fn the_rational_census_is_complete_where_a_divisor_search_would_have_to_factor() {
    // 6x^2 - 5x + 1 = (3x - 1)(2x - 1): both roots rational, neither an integer, and the
    // leading coefficient is not one. This is the case a naive "integer roots" search misses.
    let census = rational_root_census(&polynomial(&[1, -5, 6])).unwrap();
    assert_eq!(census.rational_roots, vec![rat(1, 3), rat(1, 2)]);
    assert_eq!(census.distinct_real_roots, 2);
}

#[test]
fn a_real_root_that_is_not_rational_is_retained_with_its_certificate() {
    // x^2 - 2 has two real roots and no rational root. The refusal is a population of two
    // certified irrationals, not a bool.
    let census = rational_root_census(&polynomial(&[-2, 0, 1])).unwrap();
    assert!(census.rational_roots.is_empty());
    assert_eq!(census.distinct_real_roots, 2);
    assert_eq!(census.irrational_real_roots().len(), 2);
    for root in census.irrational_real_roots() {
        assert_eq!(
            root.isolating.certificate.variations_at_lower
                - root.isolating.certificate.variations_at_upper,
            1
        );
    }
}

#[test]
fn a_polynomial_with_no_real_root_returns_an_empty_population_not_an_error() {
    let census = rational_root_census(&polynomial(&[1, 0, 1])).unwrap();
    assert_eq!(census.distinct_real_roots, 0);
    assert!(census.rational_roots.is_empty());
    assert!(census.roots.is_empty());
}

#[test]
fn a_large_constant_term_costs_a_logarithm_and_never_a_factorisation() {
    // x^2 - 1000003x + 1000002 = (x - 1)(x - 1000002). The constant term is the product of two
    // primes; a divisor enumeration would have to factor it. The bisection does not.
    let census = rational_root_census(&polynomial(&[1_000_002, -1_000_003, 1])).unwrap();
    assert_eq!(census.rational_roots, vec![integer(1), integer(1_000_002)]);
    assert!(
        census.work.bisection_steps < 64,
        "bisection is logarithmic in the bound, not linear: {} steps",
        census.work.bisection_steps
    );
}

#[test]
fn the_modular_gcd_agrees_with_the_euclidean_one_and_survives_a_large_degree() {
    let f = polynomial(&[1, -3, 2]); // (x-1)(x-2)
    let g = polynomial(&[-2, 1, 1]); // (x-1)(x+2)
    let euclid = f.monic_gcd(&g).unwrap();
    let modular = modular_monic_gcd(&f, &g).unwrap();
    assert_eq!(euclid, modular);
    assert_eq!(modular, polynomial(&[-1, 1]));
    // coprime
    assert_eq!(
        modular_monic_gcd(&polynomial(&[1, 1]), &polynomial(&[2, 1])).unwrap(),
        RationalPolynomial::one()
    );
    // a shared factor of degree 12 with large coefficients, under multipliers of degree 20
    let mut shared = RationalPolynomial::one();
    for k in 1..=12i64 {
        shared = shared.times(&polynomial(&[k * 100_003, 7, 1]));
    }
    let mut u = RationalPolynomial::one();
    let mut v = RationalPolynomial::one();
    for k in 1..=10i64 {
        u = u.times(&polynomial(&[k, -1, 3]));
        v = v.times(&polynomial(&[-k, 5, 1]));
    }
    let a = shared
        .times(&u)
        .scaled(&Rat::new(BigInt::from(3), BigInt::from(7)));
    let b = shared.times(&v);
    let modular = modular_monic_gcd(&a, &b).unwrap();
    assert_eq!(modular, shared.made_monic());
}

#[test]
fn newton_identities_round_trip_through_the_power_sums() {
    // (x-1)(x-2)(x-3)(x-4)(x-5) has power sums 5, 15, 55, 225, 979, 4425.
    let roots = [1_i64, 2, 3, 4, 5];
    let quintic = roots.iter().fold(RationalPolynomial::one(), |value, root| {
        value.times(&polynomial(&[-root, 1]))
    });
    let sums = newton_power_sums(&quintic, 5).unwrap();
    assert_eq!(
        sums,
        vec![
            integer(5),
            integer(15),
            integer(55),
            integer(225),
            integer(979),
            integer(4425)
        ]
    );
    assert_eq!(monic_from_power_sums(&sums, 5).unwrap(), quintic);
}

#[test]
fn power_sums_run_past_the_degree_by_the_linear_recurrence() {
    // x^2 - x - 1: the power sums are the Lucas numbers 2, 1, 3, 4, 7, 11, 18.
    let sums = newton_power_sums(&polynomial(&[-1, -1, 1]), 6).unwrap();
    assert_eq!(
        sums,
        vec![
            integer(2),
            integer(1),
            integer(3),
            integer(4),
            integer(7),
            integer(11),
            integer(18)
        ]
    );
}

#[test]
fn the_polynomial_resultant_eliminates_a_variable_exactly() {
    // Res_v(v - t, v^2 - 2) = t^2 - 2: substituting the first into the second.
    let first = BivariatePolynomial::new(vec![
        RationalPolynomial::new(vec![Rat::zero(), -Rat::one()]),
        RationalPolynomial::one(),
    ]);
    let second = BivariatePolynomial::new(vec![
        RationalPolynomial::constant(integer(-2)),
        RationalPolynomial::zero(),
        RationalPolynomial::one(),
    ]);
    let (resultant, work) = resultant_in_eliminated_variable(&first, &second).unwrap();
    assert_eq!(resultant, polynomial(&[-2, 0, 1]));
    assert_eq!(work.matrix_extent, 3);
}

#[test]
fn the_resultant_vanishes_identically_when_the_two_curves_share_a_component() {
    // Both carry the factor (v - t); the elimination is degenerate and says so by returning
    // the zero polynomial rather than a spurious finite root set.
    let shared = BivariatePolynomial::new(vec![
        RationalPolynomial::new(vec![Rat::zero(), -Rat::one()]),
        RationalPolynomial::one(),
    ]);
    let left = shared.times(&BivariatePolynomial::new(vec![
        RationalPolynomial::constant(integer(1)),
        RationalPolynomial::one(),
    ]));
    let right = shared.times(&BivariatePolynomial::new(vec![
        RationalPolynomial::constant(integer(2)),
        RationalPolynomial::one(),
    ]));
    let (resultant, _) = resultant_in_eliminated_variable(&left, &right).unwrap();
    assert!(resultant.is_zero());
}

#[test]
fn composition_and_reduction_agree_with_direct_evaluation() {
    let outer = polynomial(&[1, 2, 3]);
    let inner = polynomial(&[-1, 1]);
    let composed = outer.composed_with(&inner);
    for point in [-3_i64, 0, 1, 7] {
        assert_eq!(
            composed.evaluate(&integer(point)),
            outer.evaluate(&inner.evaluate(&integer(point)))
        );
    }
}

// -------------------------------------------------------------------------------------
// the root separation bound

fn constant_bivariate(polynomial: &RationalPolynomial) -> BivariatePolynomial {
    BivariatePolynomial::new(
        polynomial
            .coefficients()
            .iter()
            .map(|value| RationalPolynomial::constant(value.clone()))
            .collect(),
    )
}

/// Two independent routes to `Res(f, f')`: the Euclidean recurrence used by the bound, and the
/// Sylvester determinant by fraction-free Bareiss elimination. §2.3 — a figure deposited from
/// one route is a figure with no second reading.
#[test]
fn the_two_resultant_routes_agree_and_reproduce_the_classical_discriminants() {
    // disc(x^n + a) = (-1)^(n(n-1)/2) n^n a^(n-1), plus the two textbook small cases.
    let family: [(Vec<i64>, i64); 6] = [
        (vec![-2, 0, 1], 8),        // x^2 - 2
        (vec![-1, -1, 1], 5),       // x^2 - x - 1
        (vec![-2, 0, 0, 1], -108),  // x^3 - 2
        (vec![-6, 11, -6, 1], 4),   // (x-1)(x-2)(x-3)
        (vec![1, 0, 0, 0, 1], 256), // x^4 + 1
        (vec![-8, 12, -6, 1], 0),   // (x-2)^3, not squarefree
    ];
    let mut saw_a_vanishing_discriminant = false;
    let mut saw_both_signs = (false, false);
    for (coefficients, expected) in family {
        let rational = polynomial(&coefficients);
        let integral = rational.primitive_integer_form().unwrap();
        let (discriminant, steps) = integer_discriminant(&integral).unwrap();
        assert_eq!(
            discriminant,
            BigInt::from(expected),
            "disc of {}",
            rational.written("x")
        );
        assert!(steps > 0, "the Euclidean route took no step");

        // Route two: the Sylvester determinant, then the same normalisation.
        let derivative = rational.derivative();
        let (sylvester, _) = resultant_in_eliminated_variable(
            &constant_bivariate(&rational),
            &constant_bivariate(&derivative),
        )
        .unwrap();
        let degree = integral.degree();
        let mut by_sylvester = sylvester.coefficient(0) / rational.leading().unwrap().clone();
        if (degree * (degree - 1) / 2) % 2 == 1 {
            by_sylvester = -by_sylvester;
        }
        assert_eq!(
            by_sylvester,
            Rat::from_integer(discriminant.clone()),
            "the Euclidean and Sylvester routes disagree on {}",
            rational.written("x")
        );

        saw_a_vanishing_discriminant |= discriminant.is_zero();
        saw_both_signs.0 |= discriminant.is_positive();
        saw_both_signs.1 |= discriminant.is_negative();
    }
    assert!(
        saw_a_vanishing_discriminant && saw_both_signs.0 && saw_both_signs.1,
        "a family without a vanishing discriminant and both signs cannot exercise the sign rule"
    );
}

/// Mahler's bound, held against separations that are known exactly. The orbit is wide on
/// purpose: `sep^2` runs from `8` down to `1`, and a wrong exponent anywhere in
/// `3 |disc| / (n^(n+2) (||f||_2^2)^(n-1))` breaks one of these.
#[test]
fn the_separation_bound_lies_strictly_below_every_separation_known_exactly() {
    // (coefficients, exact sep^2)
    let family: [(Vec<i64>, Rat); 5] = [
        // x^2 - 2: roots +-sqrt2, gap 2 sqrt2.
        (vec![-2, 0, 1], integer(8)),
        // x^2 - x - 1: roots (1 +- sqrt5)/2, gap sqrt5.
        (vec![-1, -1, 1], integer(5)),
        // (x-1)(x-2)(x-3): gap 1.
        (vec![-6, 11, -6, 1], integer(1)),
        // (2x-1)(2x-3) = 4x^2 - 8x + 3: roots 1/2 and 3/2, gap 1.
        (vec![3, -8, 4], integer(1)),
        // x^2 + 1: roots +-i, gap 2 — the bound is over the COMPLEX roots, so a real-only
        // reading of it would fail here.
        (vec![1, 0, 1], integer(4)),
    ];
    let mut ratios = Vec::new();
    for (coefficients, squared_separation) in family {
        let integral = polynomial(&coefficients).primitive_integer_form().unwrap();
        let RootSeparation::Bounded(bound) = root_separation(&integral).unwrap() else {
            panic!("degree two and above is bounded");
        };
        assert!(
            bound.squared_lower_bound < squared_separation,
            "Mahler's bound {} is not below sep^2 = {squared_separation} for {}",
            bound.squared_lower_bound,
            polynomial(&coefficients).written("x")
        );
        ratios.push(squared_separation / bound.squared_lower_bound);
    }
    assert!(
        ratios.iter().any(|ratio| ratio > &integer(1000)),
        "every fixture sat within a factor of a thousand of the bound, so the check could not \
             distinguish a correct exponent from a mildly wrong one"
    );
}

/// The bound is a property of the root set, so it may not move when the polynomial is scaled:
/// `disc(cf) = c^(2n-2) disc(f)` and `||cf||_2^2 = c^2 ||f||_2^2` cancel exactly.
///
/// This is the control with the non-trivial orbit: the *discriminant* moves by `c^(2n-2)` and
/// the *norm* by `c^2`, both exhibited below, and only their combination stands still.
#[test]
fn the_separation_bound_does_not_move_when_the_polynomial_is_scaled() {
    let base = polynomial(&[-6, 11, -6, 1]);
    let RootSeparation::Bounded(unscaled) =
        root_separation(&base.primitive_integer_form().unwrap()).unwrap()
    else {
        panic!("a cubic is bounded")
    };
    let mut moved_discriminants = 0;
    for factor in [2_i64, 3, 5] {
        let scaled = IntegerPolynomial::new(
            base.coefficients()
                .iter()
                .map(|value| (value * integer(factor)).to_integer())
                .collect(),
        )
        .unwrap();
        let RootSeparation::Bounded(moved) = root_separation(&scaled).unwrap() else {
            panic!("a cubic is bounded")
        };
        // `2n - 2 = 4` and `n - 1 = 2` here, so both inputs really do move.
        assert_eq!(
            moved.discriminant,
            &unscaled.discriminant * BigInt::from(factor).pow(4)
        );
        assert_eq!(
            moved.coefficient_norm_squared,
            &unscaled.coefficient_norm_squared * BigInt::from(factor).pow(2)
        );
        assert_ne!(moved.discriminant, unscaled.discriminant);
        moved_discriminants += 1;
        // And the bound they compose to does not move at all.
        assert_eq!(moved.squared_lower_bound, unscaled.squared_lower_bound);
    }
    assert_eq!(moved_discriminants, 3);
}

#[test]
fn a_polynomial_that_is_not_squarefree_is_refused_by_its_own_vanishing_discriminant() {
    let repeated = polynomial(&[-8, 12, -6, 1]) // (x - 2)^3
        .primitive_integer_form()
        .unwrap();
    assert_eq!(
        root_separation(&repeated),
        Err(ExactPolynomialError::VanishingDiscriminant)
    );
    // A linear polynomial has one root and therefore no pair to separate. That is a statement
    // about the polynomial, not a missing bound.
    let linear = polynomial(&[-1, 2]).primitive_integer_form().unwrap();
    assert_eq!(
        root_separation(&linear).unwrap(),
        RootSeparation::NothingToSeparate { degree: 1 }
    );
    assert!(
        root_separation(&linear)
            .unwrap()
            .holds_at_most_one_root(&integer(1_000_000))
    );
}

/// The split schedule's size is read off the degree by pigeonhole, so it cannot run out — which
/// the hand-written list of thirteen fractions it replaces silently could, from degree thirteen.
#[test]
fn the_split_schedule_carries_one_more_candidate_than_the_degree_admits_roots() {
    for degree in [0_usize, 1, 5, 6, 13, 40] {
        let schedule = interior_split_schedule(degree);
        assert_eq!(schedule.len(), degree + 1);
        let distinct: std::collections::BTreeSet<_> = schedule.iter().cloned().collect();
        assert_eq!(
            distinct.len(),
            degree + 1,
            "the candidates must be distinct"
        );
        for fraction in &schedule {
            assert!(fraction.is_positive() && fraction < &Rat::one());
        }
        assert_eq!(
            worst_retained_fraction(&schedule).unwrap(),
            Rat::new(BigInt::from(degree + 1), BigInt::from(degree + 2))
        );
    }
    // The first candidate is the midpoint whenever the degree admits one exactly.
    assert_eq!(interior_split_schedule(6)[0], rat(1, 2));
    assert_eq!(interior_split_schedule(0)[0], rat(1, 2));
    // A degree-13 polynomial has fourteen candidates; the list this replaced had thirteen.
    assert_eq!(interior_split_schedule(13).len(), 14);
    assert_eq!(
        worst_retained_fraction(&[]),
        Err(ExactPolynomialError::EmptySplitSchedule)
    );
    assert_eq!(
        worst_retained_fraction(&[Rat::one()]),
        Err(ExactPolynomialError::InvalidSplitFraction)
    );
}

#[test]
fn the_shrinking_count_is_exact_and_logarithmic() {
    let half = rat(1, 2);
    // width 1 down to 1/1024 is ten halvings, and the count is taken on squares throughout.
    assert_eq!(
        squared_shrinking_steps(&integer(1), &half, &rat(1, 1_048_576)).unwrap(),
        10
    );
    assert_eq!(
        squared_shrinking_steps(&integer(1), &half, &integer(1)).unwrap(),
        0
    );
    assert_eq!(
        squared_shrinking_steps(&integer(1), &half, &integer(4)).unwrap(),
        0
    );
    // A retained fraction nearer one costs proportionally more steps, which is exactly why the
    // schedule's worst case has to be read off rather than assumed to be a half.
    let slow = squared_shrinking_steps(&integer(1), &rat(6, 7), &rat(1, 1_048_576)).unwrap();
    assert_eq!(slow, 45);
    assert_eq!(
        squared_shrinking_steps(&integer(1), &Rat::one(), &rat(1, 2)),
        Err(ExactPolynomialError::InvalidShrinkingStep)
    );
}

/// **The orbit.** Mignotte's `x^6 - 2(a x - 1)^2` has two roots about `sqrt2 * a^(-4)` apart, so
/// the isolation depth it demands is set by `a` and by nothing else. At `a = 10^12` it is under
/// the authored two hundred this replaced; at `a = 10^16` it is over, and the census now returns
/// where the authored depth refused.
#[test]
fn mignottes_family_pushes_the_isolation_past_the_depth_that_was_authored() {
    /// The level this excised. Carried here as history, never consulted by library code.
    const THE_EXCISED_DEPTH: u64 = 200;
    let mignotte = |power: u32| {
        let scale = BigInt::from(10).pow(power);
        RationalPolynomial::new(vec![
            integer(-2),
            Rat::from_integer(&scale * BigInt::from(4)),
            Rat::from_integer(-(&scale * &scale) * BigInt::from(2)),
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
            Rat::one(),
        ])
    };
    let mut under = 0;
    let mut over = 0;
    for power in [12_u32, 16] {
        let census = rational_root_census(&mignotte(power)).unwrap();
        assert_eq!(census.distinct_real_roots, 4);
        assert!(census.rational_roots.is_empty());
        // The bound is derived and the descent is inside it: that is the soundness statement,
        // and a bound that came out too small would have refused rather than returned.
        assert!(
            census.work.isolation_depth_reached < census.isolation_depth_bound,
            "10^{power}: reached {} of a permitted {}",
            census.work.isolation_depth_reached,
            census.isolation_depth_bound
        );
        if census.work.isolation_depth_reached < THE_EXCISED_DEPTH {
            under += 1;
        } else {
            over += 1;
        }
    }
    assert_eq!(
        (under, over),
        (1, 1),
        "the family must straddle the excised depth, or it separates nothing"
    );
}

#[test]
fn the_written_form_carries_no_decimal_expansion() {
    let written = RationalPolynomial::new(vec![rat(1, 3), rat(-2, 7), Rat::one()]).written("t");
    assert!(
        !written.contains('.'),
        "a float reached a presented row: {written}"
    );
    assert_eq!(written, "t^2 - (2/7)*t + (1/3)");
    assert_eq!(
        RationalPolynomial::new(vec![
            -Rat::one(),
            -Rat::one(),
            Rat::zero(),
            Rat::zero(),
            Rat::zero(),
            Rat::one()
        ])
        .written("x"),
        "x^5 - x - 1"
    );
}
