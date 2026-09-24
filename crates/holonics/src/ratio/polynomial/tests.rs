use crate::ratio::{integer, rat};
use num_traits::Zero;

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
    assert_eq!(census.roots.len(), 2);
    for root in &census.roots {
        assert_eq!(
            root.isolating.certificate.variations_at_lower
                - root.isolating.certificate.variations_at_upper,
            1
        );
    }
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
            "Mahler's bound {} is not below sep^2 = {squared_separation} for {coefficients:?}",
            bound.squared_lower_bound
        );
        ratios.push(squared_separation / bound.squared_lower_bound);
    }
    assert!(
        ratios.iter().any(|ratio| ratio > &integer(1000)),
        "every fixture sat within a factor of a thousand of the bound, so the check could not \
             distinguish a correct exponent from a mildly wrong one"
    );
}

/// Mignotte's `x^6 - 2(a x - 1)^2` has two roots about `sqrt2 * a^(-4)` apart; the census still
/// finds all four real roots, and the descent stays inside the depth bound it derives.
#[test]
fn mignottes_family_isolates_inside_its_derived_depth_bound() {
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
    }
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

// -------------------------------------------------------------------------------------------------
// the declared sizes of the monic companion, the descent's stack, and the wire's normal form
// -------------------------------------------------------------------------------------------------

/// **The factorization `Foundation/RootCount.theSquarefreePartSharesItsRoots` assumes is
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
        polynomial(&[1, -2, 1]),            // (x-1)^2
        polynomial(&[-1, 3, -3, 1]),        // (x-1)^3
        polynomial(&[2, -3, 1]),            // (x-1)(x-2)
        polynomial(&[1, 0, 1]),             // x^2+1, no real root
        polynomial(&[1, 0, 2, 0, 1]),       // (x^2+1)^2
        polynomial(&[0, 0, 1]),             // x^2
        polynomial(&[-2, 1, 2, -1, -1, 1]), // (x-1)^2 (x+1)^2 ... assorted
        polynomial(&[6, -5, 1]),            // (x-2)(x-3)
        polynomial(&[-8, 12, -6, 1]),       // (x-2)^3
        polynomial(&[4, 0, -5, 0, 1]),      // (x-1)(x+1)(x-2)(x+2)
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
            "p = gcd(p, p') * q failed on {:?}",
            source.coefficients()
        );
        assert_eq!(
            radical,
            quotient.made_monic(),
            "the radical is the monic quotient on {:?}",
            source.coefficients()
        );
        // And the conclusion: the radical has exactly the roots the polynomial has.
        for numerator in -6_i64..=6 {
            for denominator in [1_i64, 2, 3] {
                let point = rat(numerator, denominator);
                assert_eq!(
                    source.evaluate(&point).is_zero(),
                    radical.evaluate(&point).is_zero(),
                    "the radical of {:?} disagrees at {point}",
                    source.coefficients()
                );
            }
        }
    }
}
