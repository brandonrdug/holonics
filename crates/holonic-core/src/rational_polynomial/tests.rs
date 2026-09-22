use num_traits::Zero;
use relational_geometry::{integer, rat};

use crate::exact_value::STURM_DEGREE_CEILING;

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
fn polynomial_work_counts_exact_products_and_remainders() {
    let left = polynomial(&[1, 2]);
    let right = polynomial(&[3, 4]);
    let (product, product_work) = left.times_with_work(&right);
    assert_eq!(product, polynomial(&[3, 10, 8]));
    assert!(!product_work.multiplications.is_zero());
    assert!(!product_work.additions.is_zero());
    assert!(!product_work.cumulative_bits.is_zero());

    let (quotient, remainder, division_work) = product.divided_by_with_work(&left).unwrap();
    assert_eq!(quotient, right);
    assert!(remainder.is_zero());
    assert!(!division_work.divisions.is_zero());
    assert!(!division_work.cumulative_bits.is_zero());
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

// -------------------------------------------------------------------------------------------------
// the certified root enclosure
// -------------------------------------------------------------------------------------------------

/// The absolute Cauchy bound the certified enclosure replaced, for comparison in the tests below.
fn cauchy_interval(primitive: &IntegerPolynomial) -> ExactInterval {
    let degree = primitive.degree();
    let widest = primitive
        .coefficients
        .iter()
        .take(degree)
        .map(Signed::abs)
        .max()
        .unwrap_or_else(BigInt::zero);
    let leading = primitive.coefficients[degree].abs();
    let bound = (&widest + &leading - BigInt::one()) / &leading + BigInt::one();
    let half = rat(1, 2);
    ExactInterval::new(
        -Rat::from_integer(bound.clone()) - &half,
        Rat::from_integer(bound) + &half,
    )
    .expect("ordered")
}

/// **The certified enclosure encloses: it counts every root the Cauchy interval counts.**
///
/// This is the check that matters. A tighter bound that lost a root would be a silently incomplete
/// census, so the tight interval's Sturm count is held against the wide interval's on a corpus
/// shaped at the places a one-sided bound can go wrong: all roots on one side, a zero root,
/// repeated roots, a negative leading coefficient, and coefficients whose magnitudes are wildly
/// unlike their `k`-th roots.
#[test]
fn the_certified_enclosure_counts_every_root_the_cauchy_interval_counts() {
    let population: Vec<Vec<i64>> = vec![
        vec![-1, 0, 1],
        vec![1, 0, 1],
        vec![0, 0, 1],
        vec![6, -11, 6, -1],
        vec![-6, 11, -6, 1],
        vec![1, 0, 0, 0, 1],
        vec![-1, 0, 0, 0, 1],
        vec![0, 9, 7, 1],
        vec![0, 0, 9, 7, 1],
        // every root positive: `(x-1)(x-2)(x-3)(x-1000)`
        vec![6000, -11006, 6011, -1006, 1],
        // every root negative, the mirror of the same
        vec![6000, 11006, 6011, 1006, 1],
        // a huge constant term against a modest spectrum, which is the shape that made the
        // absolute Cauchy bound astronomically wide
        vec![-1_000_000_000_000, 0, 0, 0, 0, 0, 0, 0, 1],
        vec![1_000_000_000_000, 0, 0, 0, 0, 0, 0, 0, 1],
        vec![-7, 0, 0, 0, 0, 1_000_000],
    ];
    for coefficients in population {
        let source = polynomial(&coefficients);
        let primitive = source.primitive_integer_form().expect("nonzero");
        let enclosure = certified_real_root_enclosure(&primitive).expect("the enclosure returns");
        let chain = primitive.sturm_chain().expect("the chain builds");
        let wide = cauchy_interval(&primitive);
        let tight = chain
            .distinct_root_count(&enclosure.interval)
            .expect("the tight count returns");
        let broad = chain
            .distinct_root_count(&wide)
            .expect("the wide count returns");
        assert_eq!(
            tight, broad,
            "the certified enclosure of {coefficients:?} lost a root the Cauchy interval sees"
        );
        assert!(
            enclosure.interval.lower >= wide.lower && enclosure.interval.upper <= wide.upper,
            "the certified enclosure of {coefficients:?} is not inside the Cauchy interval"
        );
    }
}

/// **The two sides are counted separately.**
///
/// `(x-1)(x-2)(x-3)(x-1000)` has every root positive, so the negative side's bound reads the
/// reflection's negative coefficients — of which there are none — and comes back at `1`. A single
/// symmetric magnitude bound cannot do that, and it is the difference that matters for an operator
/// whose spectrum sits on one side of zero.
#[test]
fn the_certified_enclosure_splits_the_positive_and_negative_sides() {
    let positive = polynomial(&[6000, -11006, 6011, -1006, 1]);
    let primitive = positive.primitive_integer_form().expect("nonzero");
    let enclosure = certified_real_root_enclosure(&primitive).expect("the enclosure returns");
    assert_eq!(
        enclosure.negative_bound,
        BigInt::one(),
        "a polynomial with no negative root must not be enclosed symmetrically"
    );
    assert!(enclosure.positive_bound > BigInt::from(1000));
    assert!(enclosure.narrowing() > Rat::one());
}

/// **A `k`-th root bound is not a magnitude bound.**
///
/// `x^8 − 10^12` has its real roots at `±10^(12/8) ≈ ±31.6`, while the absolute Cauchy bound is
/// `10^12 + 1`. The enclosure is read off the eighth root and is therefore ten orders of magnitude
/// narrower, which is exactly the descent that used to be a thousand Sturm counts per root.
#[test]
fn the_certified_enclosure_reads_the_kth_root_and_not_the_magnitude() {
    let source = polynomial(&[-1_000_000_000_000, 0, 0, 0, 0, 0, 0, 0, 1]);
    let primitive = source.primitive_integer_form().expect("nonzero");
    let enclosure = certified_real_root_enclosure(&primitive).expect("the enclosure returns");
    assert!(
        enclosure.positive_bound < BigInt::from(1000),
        "the eighth root of 10^12 is about 31.6, so a bound of {} is a magnitude bound",
        enclosure.positive_bound
    );
    assert_eq!(enclosure.cauchy_bound, BigInt::from(1_000_000_000_001_i64));
    assert!(enclosure.narrowing() > Rat::from_integer(BigInt::from(1_000_000)));
    // and the roots really are inside it
    let chain = primitive.sturm_chain().expect("the chain builds");
    assert_eq!(
        chain
            .distinct_root_count(&enclosure.interval)
            .expect("counts"),
        2
    );
}

/// **A caller's declared enclosure is verified, not believed.**
///
/// The honest declaration `[0, tr Δ]` a positive semidefinite operator makes is taken and narrows
/// the descent; a declaration that does not actually enclose the roots is discarded and the owner's
/// own certified bound is used instead, so the census stays complete either way.
#[test]
fn a_declared_enclosure_is_taken_when_it_certifies_and_discarded_when_it_does_not() {
    // `(x-1)(x-2)(x-3)` with every root in `[0, 6]`.
    let source = polynomial(&[-6, 11, -6, 1]);
    let honest = ExactInterval::new(Rat::zero(), integer(6)).expect("ordered");
    let declared = rational_root_census_within(&source, &honest).expect("the census returns");
    let default = rational_root_census(&source).expect("the census returns");
    assert_eq!(declared.rational_roots, vec![integer(1), integer(2), integer(3)]);
    assert_eq!(declared.rational_roots, default.rational_roots);
    assert_eq!(declared.distinct_real_roots, default.distinct_real_roots);
    assert!(
        declared.enclosure.declared_positive,
        "6 is tighter than the owner's own upper bound of {} and certifies, so it must be adopted",
        default.enclosure.positive_bound
    );
    assert!(declared.enclosure.positive_bound <= BigInt::from(6));

    // A declaration that excludes the root at 3 does not certify, so the owner's bound stands and
    // the census still returns all three roots.
    let wrong = ExactInterval::new(Rat::zero(), integer(2)).expect("ordered");
    let refused = rational_root_census_within(&source, &wrong).expect("the census still returns");
    assert_eq!(refused.rational_roots, default.rational_roots);
    assert_eq!(refused.distinct_real_roots, 3);
    assert!(
        !refused.enclosure.declared_positive,
        "an enclosure that does not enclose must not be adopted"
    );
}

/// **The census's returned population is unchanged by the tighter bound**, on the polynomials the
/// existing tests already pin, plus a family whose roots are not rational.
#[test]
fn the_tighter_enclosure_does_not_move_the_censused_population() {
    for coefficients in [
        vec![1_i64, -5, 6],
        vec![-2, 0, 1],
        vec![1, 0, 1],
        vec![1_000_002, -1_000_003, 1],
        vec![-6, 11, -6, 1],
        vec![0, 9, 7, 1],
    ] {
        let source = polynomial(&coefficients);
        let census = rational_root_census(&source).expect("the census returns");
        // Every isolating interval holds exactly one root of the companion, and every rational root
        // is accounted for by exactly one of them.
        let companion_chain = census
            .monic_companion
            .sturm_chain()
            .expect("the chain builds");
        for root in &census.roots {
            assert_eq!(
                companion_chain
                    .distinct_root_count(&root.isolating.isolating_interval)
                    .expect("counts"),
                1,
                "an isolating interval of {coefficients:?} does not hold exactly one root"
            );
        }
        assert_eq!(census.roots.len() as u32, census.distinct_real_roots);
        for root in &census.rational_roots {
            assert!(source.evaluate(root).is_zero());
        }
        // The certified enclosure really does hold every root the descent counted.
        assert_eq!(
            companion_chain
                .distinct_root_count(&census.enclosure.interval)
                .expect("counts"),
            census.distinct_real_roots
        );
    }
}

/// **The isolation owner's declared depth has a ceiling of its own.**
#[test]
fn the_isolation_depth_declaration_is_refused_above_the_owners_ceiling() {
    let source = polynomial(&[-6, 11, -6, 1]);
    let primitive = source.primitive_integer_form().expect("nonzero");
    let enclosure = certified_real_root_enclosure(&primitive).expect("the enclosure returns");
    assert_eq!(
        isolate_real_roots(&primitive, &enclosure.interval, u32::MAX),
        Err(ExactPolynomialError::IsolationDepthBoundTooLarge {
            bound: u32::MAX,
            ceiling: ISOLATION_DEPTH_CEILING,
        })
    );
    let isolated =
        isolate_real_roots(&primitive, &enclosure.interval, 32).expect("the isolation returns");
    assert_eq!(isolated.len(), 3);
    for pair in isolated.windows(2) {
        assert!(pair[0].upper <= pair[1].lower, "the intervals must be ascending and disjoint");
    }
}

/// **The half-plane counter is this module's, and it counts.**
///
/// `causal_chord` holds it against Sylvester's signature on symmetric operators; this is the
/// polynomial-level check at the owner, including the Cauchy index's sign, which is the one thing a
/// signed remainder sequence can get wrong without failing anywhere else.
#[test]
fn the_half_plane_counter_places_declared_populations() {
    // `(x+1)(x+2)(x+3)`: Hurwitz.
    let count = half_plane_count(&polynomial(&[6, 11, 6, 1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (3, 0, 0));
    assert!(count.is_hurwitz());
    // `(x-1)(x+1)(x^2+1)`: one right, one left, two on the axis.
    let count = half_plane_count(&polynomial(&[-1, 0, 0, 0, 1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (1, 2, 1));
    assert_eq!(count.total(), 4);
    // the sign of the index is live: `(x-1)(x-2)(x-3)` is the reflection of the Hurwitz case
    let count = half_plane_count(&polynomial(&[-6, 11, -6, 1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (0, 0, 3));
    // a negative leading coefficient names the same population
    let count = half_plane_count(&polynomial(&[-6, -11, -6, -1])).expect("the count returns");
    assert_eq!((count.left, count.axis, count.right), (3, 0, 0));
}

/// **The Cauchy index is a signed reading and its sign is relative to the pair.**
///
/// `I(q/p)` and `I(-q/p)` differ by sign, which is the defect a numerator normalized to a positive
/// leading coefficient would introduce and which nothing else in the half-plane count would catch.
#[test]
fn the_cauchy_index_flips_when_only_the_numerator_flips() {
    let denominator = polynomial(&[-1, 0, 1]);
    let numerator = polynomial(&[0, 1]);
    let index = cauchy_index(&numerator, &denominator).expect("the index returns");
    let flipped = cauchy_index(&numerator.negated(), &denominator).expect("the index returns");
    assert_eq!(index, -flipped);
    assert_ne!(index, 0, "a zero index would make this test vacuous");
}

/// **A remounted enclosure passes through its constructor.**
///
/// The enclosure's interval and its two bounds are one statement written twice, so a wire that
/// disagrees with itself is refused rather than reconstructed. A lawful one round-trips.
#[test]
fn a_root_enclosure_wire_that_disagrees_with_itself_is_refused() {
    let source = polynomial(&[-6, 11, -6, 1]);
    let primitive = source.primitive_integer_form().expect("nonzero");
    let lawful = certified_real_root_enclosure(&primitive).expect("the enclosure returns");
    let wire = serde_json::to_string(&lawful).expect("serialized");
    let remounted: RealRootEnclosure = serde_json::from_str(&wire).expect("a lawful wire");
    assert_eq!(remounted, lawful);

    // a bound that no longer agrees with the interval the same wire carries
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("a lawful wire");
    hostile["positive_bound"] =
        serde_json::to_value(&lawful.positive_bound + BigInt::one()).expect("serialized");
    assert!(serde_json::from_value::<RealRootEnclosure>(hostile).is_err());

    // a claim to be wider than the Cauchy bound the same wire reports
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("a lawful wire");
    hostile["cauchy_bound"] = serde_json::to_value(BigInt::one()).expect("serialized");
    assert!(serde_json::from_value::<RealRootEnclosure>(hostile).is_err());

    // a non-positive bound is not a bound
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("a lawful wire");
    hostile["negative_bound"] = serde_json::to_value(BigInt::zero()).expect("serialized");
    assert!(serde_json::from_value::<RealRootEnclosure>(hostile).is_err());
}

/// **The declared sizes are refused at the enclosure as they are at the chain.**
#[test]
fn the_enclosure_refuses_a_declared_size_above_the_owners_ceiling() {
    let mut tall = vec![BigInt::zero(); STURM_DEGREE_CEILING + 2];
    tall[0] = -BigInt::one();
    tall[STURM_DEGREE_CEILING + 1] = BigInt::one();
    let source = IntegerPolynomial::new(tall).expect("nonzero");
    assert!(matches!(
        certified_real_root_enclosure(&source),
        Err(ExactPolynomialError::Value(
            ExactValueError::SturmDegreeTooLarge { .. }
        ))
    ));
}

// -------------------------------------------------------------------------------------------------
// the declared sizes of the monic companion, the descent's stack, and the wire's normal form
// -------------------------------------------------------------------------------------------------

/// **The companion's width is refused before the companion is formed.**
///
/// The descent builds `a_i · c^(n-1-i)` for exponents up to `degree - 1`; with a degree-100
/// polynomial and a sixty-four-bit leading coefficient that product alone reaches six thousand
/// bits, and the Sturm chain over it did not finish in sixty seconds. The refusal is asserted **by
/// name** rather than by a clock: `MonicCompanionTooWide` is produced only by
/// `check_companion_declared_size`, which reads bit counts and forms nothing, so reaching it is
/// itself the proof that no companion coefficient, no Sturm chain and no enclosure was allocated
/// first.
#[test]
fn an_over_ceiling_monic_companion_is_refused_before_it_is_formed() {
    let leading: BigInt = (BigInt::one() << 63_usize) | BigInt::one();
    let mut coefficients = vec![Rat::one(); 101];
    coefficients[100] = Rat::from_integer(leading.clone());
    let heavy = RationalPolynomial::new(coefficients);

    match rational_root_census(&heavy) {
        Err(ExactPolynomialError::MonicCompanionTooWide {
            degree,
            leading_bits,
            bits,
            ceiling,
        }) => {
            assert_eq!(degree, 100);
            assert_eq!(leading_bits, 64);
            assert_eq!(bits, 100 * 64);
            assert_eq!(ceiling, MONIC_COMPANION_BIT_CEILING);
        }
        other => panic!("the blow-up was not refused before it was formed: {other:?}"),
    }

    // The gated path is unchanged: the same degree with a unit leading coefficient has a companion
    // that *is* the polynomial, and it returns.
    let mut coefficients = vec![Rat::zero(); 101];
    coefficients[0] = -Rat::one();
    coefficients[100] = Rat::one();
    let monic = RationalPolynomial::new(coefficients);
    let census = rational_root_census(&monic).expect("a monic degree-100 census returns");
    assert_eq!(census.rational_roots, vec![Rat::one(), -Rat::one()]
        .into_iter()
        .collect::<std::collections::BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>());

    // And the gate itself is reachable without a census at all, on declared numbers alone.
    let primitive = heavy
        .primitive_integer_form()
        .expect("a primitive integer form");
    let leading = primitive
        .coefficients
        .last()
        .cloned()
        .expect("a leading coefficient");
    assert!(matches!(
        check_companion_declared_size(&primitive, &leading),
        Err(ExactPolynomialError::MonicCompanionTooWide { .. })
    ));
}

/// **A splitting depth read off the material is still a declared size, and is refused before the
/// isolation descends.**
///
/// The derived bound grows like `(n^2 - 1) * bits`: `x^12 + x - 2^4000` derives about 198000,
/// which is past the ceiling, while `x^6 + x - 2^4000` derives 51919 and is admitted. Nothing that
/// this repository's own material derives is refused; what is refused is an unbounded `u64` the
/// descent would otherwise simply take.
#[test]
fn a_splitting_depth_past_the_ceiling_is_refused_before_the_descent() {
    let deep = |degree: usize| {
        let mut coefficients = vec![Rat::zero(); degree + 1];
        coefficients[0] = Rat::from_integer(-(BigInt::one() << 4000_usize));
        coefficients[1] = Rat::one();
        coefficients[degree] = Rat::one();
        RationalPolynomial::new(coefficients)
    };
    match rational_root_census(&deep(12)) {
        Err(ExactPolynomialError::SeparationSplittingDepthTooLarge { bound, ceiling }) => {
            assert!(
                bound > ceiling,
                "the refusal must name a bound above the ceiling, got {bound} against {ceiling}"
            );
            assert_eq!(ceiling, SEPARATION_SPLITTING_DEPTH_CEILING);
        }
        other => panic!("an unbounded splitting depth was not refused: {other:?}"),
    }
    // And the material that stays inside the ceiling is admitted, bound and all.
    let census = rational_root_census(&deep(6)).expect("a bound inside the ceiling is admitted");
    assert!(census.isolation_depth_bound > 10_000);
    assert!(census.isolation_depth_bound <= SEPARATION_SPLITTING_DEPTH_CEILING);
}

/// **Neither descent runs on the machine stack.**
///
/// Both were genuinely recursive, with the depth coming from the caller's own coefficients:
/// `x² − 2^4000` has roots at `±2^2000`, so the half-integer descent has to halve an interval of
/// width `2^2001` and the recursion reached two thousand frames. This runs the whole census on a
/// thread with a 192 KiB stack — far below what two thousand frames of that function need — so a
/// recursive implementation aborts here and a worklist returns. An abort is not a catchable
/// failure, which is exactly why the recursion had to go.
#[test]
fn the_census_descends_on_worklists_and_not_on_the_machine_stack() {
    let handle = std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let far = RationalPolynomial::new(vec![
                Rat::from_integer(-(BigInt::one() << 4000_usize)),
                Rat::zero(),
                Rat::one(),
            ]);
            let census = rational_root_census(&far).expect("the census returns");
            (census.distinct_real_roots, census.work.bisection_steps)
        })
        .expect("the thread spawns");
    let (roots, bisections) = handle.join().expect("a worklist descent does not overflow a stack");
    assert_eq!(roots, 2, "±2^2000 are two distinct real roots");
    assert!(
        bisections > 1000,
        "the descent must actually be deep for this to prove anything; it took {bisections} steps"
    );
}

/// **A chain belongs to one polynomial at this owner too.**
#[test]
fn isolating_against_a_chain_built_for_another_polynomial_is_refused() {
    let linear = IntegerPolynomial::new(vec![BigInt::zero(), BigInt::one()]).expect("nonzero");
    let no_real_root = IntegerPolynomial::new(vec![BigInt::one(), BigInt::zero(), BigInt::one()])
        .expect("nonzero");
    let chain = linear.sturm_chain().expect("the chain builds");
    let enclosure = ExactInterval::new(
        Rat::from_integer(BigInt::from(-2)),
        Rat::from_integer(BigInt::from(2)),
    )
    .expect("ordered");

    assert!(matches!(
        isolate_against_chain(&no_real_root, &chain, &enclosure, 16),
        Err(ExactPolynomialError::Value(
            ExactValueError::ChainPolynomialMismatch { .. }
        ))
    ));
    // The chain alone cannot be mispaired, and it isolates the one root of `x`.
    let (intervals, _) = isolate_with_chain(&chain, &enclosure, 16).expect("the chain isolates");
    assert_eq!(intervals.len(), 1);
    // The lawful pairing is unchanged.
    let (again, _) =
        isolate_against_chain(&linear, &chain, &enclosure, 16).expect("the lawful pairing");
    assert_eq!(again, intervals);
}

/// **An untrimmed rational polynomial is refused at the wire.**
///
/// The derived `Deserialize` skipped `new`'s trim, so the remounted instance reported a degree one
/// too high — and `degree()` is what every division, gcd and census reads first.
#[test]
fn an_untrimmed_rational_polynomial_wire_is_refused_and_a_lawful_one_round_trips() {
    let lawful = polynomial(&[1, 2, 3]);
    let wire = serde_json::to_string(&lawful).expect("serialized");
    assert_eq!(
        serde_json::from_str::<RationalPolynomial>(&wire).expect("a lawful wire"),
        lawful
    );

    // Public-field construction is not available here, so the untrimmed wire is built from the
    // lawful one's own shape.
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    let coefficients = hostile["coefficients"]
        .as_array_mut()
        .expect("an array of coefficients");
    coefficients.push(serde_json::to_value(Rat::zero()).expect("serialized"));
    let refusal = serde_json::from_value::<RationalPolynomial>(hostile)
        .expect_err("a zero leading coefficient is not the normal form");
    assert!(
        refusal.to_string().contains("leading entry is zero"),
        "the untrimmed wire was refused for the wrong reason: {refusal}"
    );

    // The zero polynomial's own normal form is the empty list, and that still remounts.
    let zero = RationalPolynomial::zero();
    let wire = serde_json::to_string(&zero).expect("serialized");
    assert_eq!(
        serde_json::from_str::<RationalPolynomial>(&wire).expect("the zero polynomial remounts"),
        zero
    );
    assert_eq!(RationalPolynomial::default(), zero);
}

/// **The factorization `Foundation/RootCount.lean::theSquarefreePartSharesItsRoots` assumes is
/// checked, at every use, on real material.**
///
/// The Lean theorem takes `p = gcd(p, p') · q` as a hypothesis. `squarefree_part` discharges it by
/// taking an *exact* division that refuses a nonzero remainder, so the hypothesis holds by
/// construction; this holds the identity against a corpus as well, and checks the conclusion the
/// theorem states — that the radical has exactly the roots of the polynomial — where the roots are
/// known by hand.
#[test]
fn the_squarefree_factorization_the_lean_theorem_assumes_is_checked() {
    let corpus: Vec<RationalPolynomial> = vec![
        polynomial(&[-1, 1]),
        polynomial(&[1, -2, 1]),                   // (x-1)^2
        polynomial(&[-1, 3, -3, 1]),               // (x-1)^3
        polynomial(&[2, -3, 1]),                   // (x-1)(x-2)
        polynomial(&[1, 0, 1]),                    // x^2+1, no real root
        polynomial(&[1, 0, 2, 0, 1]),              // (x^2+1)^2
        polynomial(&[0, 0, 1]),                    // x^2
        polynomial(&[-2, 1, 2, -1, -1, 1]),        // (x-1)^2 (x+1)^2 ... assorted
        polynomial(&[6, -5, 1]),                   // (x-2)(x-3)
        polynomial(&[-8, 12, -6, 1]),              // (x-2)^3
        polynomial(&[4, 0, -5, 0, 1]),             // (x-1)(x+1)(x-2)(x+2)
    ];
    for source in corpus {
        let gcd = source
            .monic_gcd(&source.derivative())
            .expect("the gcd returns");
        let radical = source.squarefree_part().expect("the radical returns");
        // `squarefree_part` returns the monic quotient; the hypothesis is about the quotient
        // itself, and monic scaling is a unit.
        let quotient = source
            .divided_exactly_by(&gcd)
            .expect("the division the library takes is exact");
        assert_eq!(
            gcd.times(&quotient),
            source,
            "p = gcd(p, p') * q failed on {}",
            source.written("x")
        );
        assert_eq!(
            radical,
            quotient.made_monic(),
            "the radical is the monic quotient on {}",
            source.written("x")
        );
        // And the conclusion: the radical has exactly the roots the polynomial has.
        for numerator in -6_i64..=6 {
            for denominator in [1_i64, 2, 3] {
                let point = rat(numerator, denominator);
                assert_eq!(
                    source.evaluate(&point).is_zero(),
                    radical.evaluate(&point).is_zero(),
                    "the radical of {} disagrees at {point}",
                    source.written("x")
                );
            }
        }
    }
}

/// **Every remaining certificate-carrying wire in this owner is closed.**
///
/// Each type round-trips from a lawful instance built by the real entry point, and each hand-
/// tampered wire is refused by name. These are the types the sweep found still reconstructible
/// past their own invariants: a separation bound whose number nobody recomputed, a half-plane
/// count whose three populations did not partition the degree, a bivariate polynomial with an
/// untrimmed leading coefficient, and the census itself.
#[test]
fn the_certificate_carrying_wires_of_this_owner_are_closed() {
    // --- the root separation bound: re-derived from its own material -----------------------
    let squarefree = IntegerPolynomial::new(vec![
        BigInt::from(-6),
        BigInt::from(11),
        BigInt::from(-6),
        BigInt::one(),
    ])
    .expect("nonzero");
    let separation = root_separation(&squarefree).expect("a bound");
    let wire = serde_json::to_string(&separation).expect("serialized");
    assert_eq!(
        serde_json::from_str::<RootSeparation>(&wire).expect("a lawful wire"),
        separation
    );
    // A *larger* declared floor makes `holds_at_most_one_root` say yes where it must say no,
    // which `isolate_within` then reports as a Sturm/discriminant contradiction that is not one.
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["Bounded"]["squared_lower_bound"] =
        serde_json::to_value(Rat::one()).expect("serialized");
    let refusal = serde_json::from_value::<RootSeparation>(hostile)
        .expect_err("a bound nobody derived is refused");
    assert!(
        refusal.to_string().contains("its own material derives"),
        "refused for the wrong reason: {refusal}"
    );
    // And "nothing to separate" may not be claimed of a degree that has a pair of roots.
    let hostile = serde_json::json!({ "NothingToSeparate": { "degree": 5 } });
    assert!(
        serde_json::from_value::<RootSeparation>(hostile)
            .err()
            .is_some_and(|refusal| refusal.to_string().contains("pair of roots")),
        "a degree with a pair of roots may not claim there is nothing to separate"
    );
    assert!(
        serde_json::from_value::<RootSeparation>(
            serde_json::json!({ "NothingToSeparate": { "degree": 1 } })
        )
        .is_ok()
    );

    // --- the half-plane count: the three populations partition the degree -------------------
    let stable = polynomial(&[2, 3, 1]);
    let count = half_plane_count(&stable).expect("the count");
    let wire = serde_json::to_string(&count).expect("serialized");
    assert_eq!(
        serde_json::from_str::<HalfPlaneCount>(&wire).expect("a lawful wire"),
        count
    );
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["left"] = serde_json::Value::from(count.left + 1);
    assert!(
        serde_json::from_value::<HalfPlaneCount>(hostile)
            .err()
            .is_some_and(|refusal| refusal.to_string().contains("partition the roots")),
        "three populations that do not partition the degree must be refused"
    );

    // --- the bivariate polynomial: the same trimmed normal form -----------------------------
    let bivariate = BivariatePolynomial::new(vec![polynomial(&[1, 1]), polynomial(&[0, 2])]);
    let wire = serde_json::to_string(&bivariate).expect("serialized");
    assert_eq!(
        serde_json::from_str::<BivariatePolynomial>(&wire).expect("a lawful wire"),
        bivariate
    );
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["coefficients"]
        .as_array_mut()
        .expect("an array")
        .push(serde_json::to_value(RationalPolynomial::zero()).expect("serialized"));
    assert!(
        serde_json::from_value::<BivariatePolynomial>(hostile)
            .err()
            .is_some_and(|refusal| refusal.to_string().contains("leading entry is zero")),
        "an untrimmed bivariate wire must be refused"
    );

    // --- the census: re-derived where the data to re-derive it is present --------------------
    let source = polynomial(&[-2, 1, 2, 1]);
    let census = rational_root_census(&source).expect("the census");
    let wire = serde_json::to_string(&census).expect("serialized");
    assert_eq!(
        serde_json::from_str::<RationalRootCensus>(&wire).expect("a lawful wire"),
        census
    );
    // A companion nobody generated.
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["monic_companion"] = serde_json::to_value(
        IntegerPolynomial::new(vec![BigInt::one(), BigInt::one()]).expect("nonzero"),
    )
    .expect("serialized");
    assert!(
        serde_json::from_value::<RationalRootCensus>(hostile)
            .err()
            .is_some_and(|refusal| refusal.to_string().contains("does not agree with itself")),
        "a companion nobody generated must be refused"
    );
    // A rational root that is not a root.
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["rational_roots"] =
        serde_json::to_value(vec![rat(1, 7)]).expect("serialized");
    assert!(
        serde_json::from_value::<RationalRootCensus>(hostile)
            .err()
            .is_some_and(|refusal| {
                let text = refusal.to_string();
                text.contains("did not vanish") || text.contains("does not agree with itself")
            }),
        "a declared rational root that is not a root must be refused"
    );
    // A declared real-root count that does not match the isolated population.
    let mut hostile: serde_json::Value = serde_json::from_str(&wire).expect("the lawful wire");
    hostile["distinct_real_roots"] =
        serde_json::Value::from(census.distinct_real_roots + 3);
    assert!(
        serde_json::from_value::<RationalRootCensus>(hostile)
            .err()
            .is_some_and(|refusal| refusal.to_string().contains("does not agree with itself")),
        "a count that does not match the isolated population must be refused"
    );
}
