//! Tests for the Iwasawa tower.
//!
//! Every assertion below has a computed value behind it. No test asserts a shape that the test
//! itself supplied, and every expected number was produced by an exact computation over `BigInt`
//! — the Smith normal form of an assembled relation matrix, or an exact polynomial division.
//!
//! The negative tests are grouped at the top of each section and are named for the refusal they
//! fire.

use super::*;
use crate::continuing_tower::{ComposedTransition, check_restriction_laws};

fn ints(values: &[i64]) -> Vec<BigInt> {
    values.iter().map(|value| BigInt::from(*value)).collect()
}

fn big(value: u64) -> BigUint {
    BigUint::from(value)
}

fn level(prime: u64, n: u32) -> IwasawaLevel {
    IwasawaLevel::new(prime, n).expect("test fixture: the level is inside the declared bounds")
}

fn presented(generators: &[&[i64]]) -> LambdaPresentation {
    LambdaPresentation::new(generators.iter().map(|g| ints(g)).collect())
        .expect("test fixture: the presentation is inside the declared bounds")
}

// -------------------------------------------------------------------------------------------
// 1. The declared parameters and their refusals.
// -------------------------------------------------------------------------------------------

#[test]
fn the_level_constructor_refuses_a_composite_prime() {
    assert_eq!(
        IwasawaLevel::new(9, 1),
        Err(IwasawaRefusal::NotPrime { prime: 9 })
    );
    assert_eq!(
        IwasawaLevel::new(1_042_441, 1),
        Err(IwasawaRefusal::PrimeTooLarge {
            prime: 1_042_441,
            bound: MAX_PRIME
        }),
        "1021^2 is refused for its SIZE, before any trial division: the primality loop is never \
         sized by the declaration"
    );
    assert_eq!(
        IwasawaLevel::new(1, 0),
        Err(IwasawaRefusal::NotPrime { prime: 1 })
    );
    assert_eq!(
        IwasawaLevel::new(0, 0),
        Err(IwasawaRefusal::NotPrime { prime: 0 })
    );
    assert_eq!(
        IwasawaLevel::new(1001, 0),
        Err(IwasawaRefusal::NotPrime { prime: 1001 }),
        "1001 = 7 · 11 · 13 is below MAX_PRIME, so it reaches the trial division and fails there"
    );
}

#[test]
fn the_level_constructor_refuses_a_prime_above_the_bound() {
    // 1031 is prime and above MAX_PRIME = 1021.
    assert_eq!(
        IwasawaLevel::new(1031, 0),
        Err(IwasawaRefusal::PrimeTooLarge {
            prime: 1031,
            bound: MAX_PRIME
        })
    );
    // 1021 itself is prime and accepted, with degree 1 at level 0 and 1021 at level 1.
    assert_eq!(level(1021, 0).degree(), 1);
    assert_eq!(level(1021, 1).degree(), 1021);
    assert_eq!(
        IwasawaLevel::new(1021, 2),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 1021,
            level: 2,
            bound: MAX_DEGREE
        })
    );
}

#[test]
fn the_level_constructor_refuses_an_overflowing_or_oversized_degree() {
    // p^n overflows u64 long before it reaches MAX_DEGREE: `checked_pow` returns None and the
    // refusal is typed rather than a wrapped degree.
    assert_eq!(
        IwasawaLevel::new(1021, 1_000_000),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 1021,
            level: 1_000_000,
            bound: MAX_DEGREE
        })
    );
    // 2^12 = 4096 = MAX_DEGREE is accepted; 2^13 is not.
    assert_eq!(level(2, 12).degree(), 4096);
    assert_eq!(
        IwasawaLevel::new(2, 13),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 2,
            level: 13,
            bound: MAX_DEGREE
        })
    );
    assert_eq!(level(3, 7).degree(), 2187);
    assert_eq!(
        IwasawaLevel::new(3, 8),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 3,
            level: 8,
            bound: MAX_DEGREE
        })
    );
}

#[test]
fn no_accepted_level_has_degree_zero() {
    // A degree-zero level is unreachable rather than refused: p^n = 1 at n = 0 for every prime and
    // p^n ≥ 2 above it. ω_0 = T has degree 1, so Z[T]/(ω_0) has basis {1}.
    for prime in [2_u64, 3, 5, 7, 1021] {
        assert_eq!(level(prime, 0).degree(), 1);
        assert_eq!(omega(&level(prime, 0)), ints(&[0, 1]), "ω_0 = T");
    }
}

#[test]
fn the_successor_re_enters_the_constructor() {
    assert_eq!(
        level(2, 12).successor(),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 2,
            level: 13,
            bound: MAX_DEGREE
        }),
        "the successor of the top accepted level is refused, not silently truncated"
    );
    assert_eq!(
        level(3, 2).successor().expect("3^3 is inside the bound"),
        level(3, 3)
    );
}

// -------------------------------------------------------------------------------------------
// 2. ω_n, distinguishedness, and the divisibility chain.
// -------------------------------------------------------------------------------------------

#[test]
fn omega_is_the_binomial_row_with_the_constant_removed() {
    assert_eq!(omega(&level(3, 0)), ints(&[0, 1]));
    assert_eq!(omega(&level(3, 1)), ints(&[0, 3, 3, 1]));
    assert_eq!(
        omega(&level(3, 2)),
        ints(&[0, 9, 36, 84, 126, 126, 84, 36, 9, 1])
    );
    assert_eq!(omega(&level(2, 1)), ints(&[0, 2, 1]));
    assert_eq!(omega(&level(2, 2)), ints(&[0, 4, 6, 4, 1]));
    assert_eq!(omega(&level(5, 1)), ints(&[0, 5, 10, 10, 5, 1]));
}

#[test]
fn omega_is_distinguished_at_every_checked_level() {
    for (prime, top) in [(2_u64, 5_u32), (3, 4), (5, 3), (7, 3), (11, 2)] {
        for n in 0..=top {
            let chart = level(prime, n);
            let receipt = check_distinguished(&chart);
            assert!(
                receipt.is_distinguished(),
                "ω_{n} at p={prime} is not distinguished: {receipt:?}"
            );
            assert!(receipt.is_monic());
            assert!(receipt.constant_is_zero());
            assert_eq!(receipt.degree(), chart.degree());
            assert_eq!(
                receipt.middle_coefficients_checked(),
                chart.degree() - 1,
                "every coefficient strictly between the constant and the leading one is divided"
            );
            assert!(receipt.all_middle_divisible_by_prime());
        }
    }
}

#[test]
fn the_distinguished_receipt_names_its_own_extent() {
    // At p = 3, n = 2 the middle coefficients are 9, 36, 84, 126, 126, 84, 36, 9: eight of them,
    // each divisible by 3. The receipt reports that count, so the claim has a stated extent.
    let receipt = check_distinguished(&level(3, 2));
    assert_eq!(receipt.middle_coefficients_checked(), 8);
    assert_eq!(receipt.level(), &level(3, 2));
    let coefficients = omega(&level(3, 2));
    let checked: Vec<BigInt> = coefficients[1..9].to_vec();
    assert_eq!(checked, ints(&[9, 36, 84, 126, 126, 84, 36, 9]));
    for coefficient in &checked {
        assert!((coefficient % BigInt::from(3)).is_zero());
    }
}

#[test]
fn omega_divides_omega_succ_exactly() {
    for (prime, top) in [(2_u64, 4_u32), (3, 3), (5, 2), (7, 2)] {
        for n in 0..top {
            let chart = level(prime, n);
            let division = omega_divides_omega_succ(&chart).expect("the successor is in bounds");
            assert!(
                division.divides(),
                "ω_{n} does not divide ω_{} at p={prime}: remainder {:?}",
                n + 1,
                division.remainder()
            );
            assert!(division.remainder().is_empty());
            assert_eq!(division.coarse(), &chart);
            assert_eq!(
                degree_of(division.quotient()),
                Some(division.fine().degree() - chart.degree()),
                "the quotient has degree p^(n+1) - p^n"
            );
            // The division is the claim; multiply back and compare with ω_(n+1).
            let reconstructed = poly_mul(&omega(&chart), division.quotient());
            assert_eq!(reconstructed, trim(omega(division.fine())));
        }
    }
}

#[test]
fn the_quotient_agrees_with_the_geometric_series() {
    // `omega_divides_omega_succ` performs the actual polynomial division. This is the independent
    // route: with Y = (1+T)^(p^n), ω_(n+1) = Y^p - 1 and ω_n = Y - 1, so the quotient is Σ_(j<p) Y^j.
    for (prime, top) in [(2_u64, 4_u32), (3, 3), (5, 2), (7, 2)] {
        for n in 0..top {
            let chart = level(prime, n);
            let by_division = omega_divides_omega_succ(&chart).expect("in bounds");
            let by_identity = omega_quotient_by_identity(&chart).expect("in bounds");
            assert_eq!(
                by_division.quotient(),
                by_identity.as_slice(),
                "the two routes disagree at p={prime}, n={n}"
            );
        }
    }
}

// -------------------------------------------------------------------------------------------
// 3. Composition with the wave-1 continuing tower.
// -------------------------------------------------------------------------------------------

#[test]
fn the_tower_satisfies_the_wave_one_restriction_laws() {
    let tower = IwasawaTower::new(3, 2).expect("3^2 = 9 is inside the bound");
    assert_eq!(tower.prime(), 3);
    assert_eq!(tower.max_level(), 2);
    let charts = tower.charts();
    let faces: Vec<(u32, Vec<BigInt>)> = vec![
        (0, Vec::new()),
        (0, ints(&[5])),
        (1, ints(&[1, 2])),
        (1, ints(&[-4, 0, 7])),
        (2, ints(&[1, -2, 3, 0, 0, 0, 0, 0, 4])),
        (2, ints(&[0, 0, 0, 0, 0, 0, 0, 0, 1])),
    ];
    let receipt = check_restriction_laws(&tower, &charts, &faces)
        .expect("restrict_refl and restrict_trans hold on this aperture");
    assert_eq!(receipt.faces_checked, 6);
    assert_eq!(receipt.reflexive_charts.len(), 6);
    // Weakly increasing triples (coarse ⊑ middle ⊑ fine) over three charts: ten of them, and each
    // has at least one face above its `fine`.
    assert_eq!(receipt.transitive_triples.len(), 10);
    assert!(receipt.transitive_triples.contains(&(0, 1, 2)));
}

#[test]
fn the_tower_refuses_a_face_it_does_not_carry_and_a_non_refinement() {
    let tower = IwasawaTower::new(3, 2).expect("in bounds");
    // Degree 9 is p^2, so a ten-coefficient vector is not a canonical face at chart 2.
    let too_long = ints(&[1, 0, 0, 0, 0, 0, 0, 0, 0, 1]);
    assert!(!tower.carries(&2, &too_long));
    assert_eq!(
        tower.restrict(&1, &2, &too_long),
        Err(TowerRefusal::FaceNotCarried {
            chart: 2,
            face: too_long
        })
    );
    // An untrimmed representative is not a face either: the tower's face equality is `Eq` on the
    // vector, so a trailing zero would be a second name for one class.
    assert!(!tower.carries(&1, &ints(&[1, 2, 0])));
    // Restricting from coarse to fine is not a restriction.
    assert_eq!(
        tower.restrict(&2, &1, &ints(&[1, 2])),
        Err(TowerRefusal::NotARefinement { coarse: 2, fine: 1 })
    );
    // A chart the tower does not carry.
    assert!(tower.level(3).is_none());
    assert!(tower.omega_at(3).is_none());
    assert!(!tower.carries(&3, &ints(&[1])));
}

#[test]
fn the_omega_restriction_reopens_every_source() {
    let restriction = OmegaRestriction::new(level(3, 1), level(3, 2)).expect("1 ⊑ 2 at p = 3");
    assert_eq!(restriction.coarse(), &level(3, 1));
    assert_eq!(restriction.fine(), &level(3, 2));
    let sources: Vec<Vec<BigInt>> = vec![
        Vec::new(),
        ints(&[7]),
        ints(&[0, 0, 1]),
        ints(&[1, -2, 3, 0, 0, 0, 0, 0, 4]),
        // Deliberately of degree far above p^2: `apply` is total on every integer polynomial.
        ints(&[-5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 11]),
        ints(&[-1, -1, -1, -1, -1, -1, -1, -1, -1, -1]),
    ];
    for source in &sources {
        let receipt = restriction
            .check_reopen(source)
            .unwrap_or_else(|refusal| panic!("reopen failed on {source:?}: {refusal}"));
        assert_eq!(receipt.sources_reopened, 1);
        // The transported face really is smaller than the source's own level.
        assert!(restriction.apply(source).len() <= level(3, 1).degree());
    }
}

#[test]
fn the_restriction_residual_is_what_separates_two_merged_sources() {
    let restriction = OmegaRestriction::new(level(3, 1), level(3, 2)).expect("in bounds");
    let left = ints(&[1, 2]);
    let right = poly_add(&left, &omega(&level(3, 1))); // differs from `left` by exactly ω_1
    assert_eq!(right, ints(&[1, 5, 3, 1]));
    assert_ne!(left, right);
    assert_eq!(restriction.apply(&left), restriction.apply(&right));
    let (residual_left, residual_right) = restriction
        .separating_residuals(&left, &right)
        .expect("the two sources are merged by the transported face");
    assert_ne!(residual_left, residual_right);
    assert_eq!(residual_left, Vec::<BigInt>::new());
    assert_eq!(residual_right, ints(&[1]));
    // The later, finer receiver reads the source back off the transported face plus the residual.
    let recovered = restriction.reopen_later_receiver(
        &restriction.apply(&right),
        &residual_right,
        &|source: &Vec<BigInt>| source.clone(),
    );
    assert_eq!(recovered, right);
}

#[test]
fn two_restrictions_compose_to_the_direct_one() {
    // ω_0 | ω_1 | ω_2, so reducing twice is reducing once. The composite's residual is the PAIR of
    // component residuals, which is the wave-1 `Transition.comp_residual`.
    let upper = OmegaRestriction::new(level(3, 1), level(3, 2)).expect("in bounds");
    let lower = OmegaRestriction::new(level(3, 0), level(3, 1)).expect("in bounds");
    let direct = OmegaRestriction::new(level(3, 0), level(3, 2)).expect("in bounds");
    let composed = ComposedTransition::new(lower, upper);
    let sources: Vec<Vec<BigInt>> = vec![
        ints(&[1, -2, 3, 0, 0, 0, 0, 0, 4]),
        ints(&[5, 5, 5]),
        ints(&[0, 0, 0, 0, 0, 0, 0, 0, 1]),
        Vec::new(),
    ];
    for source in &sources {
        assert_eq!(
            composed.apply(source),
            direct.apply(source),
            "restricting 2 → 1 → 0 disagrees with 2 → 0 on {source:?}"
        );
        let receipt = composed
            .check_reopen(source)
            .unwrap_or_else(|refusal| panic!("composite reopen failed: {refusal}"));
        assert_eq!(receipt.sources_reopened, 1);
    }
}

#[test]
fn the_restriction_refuses_a_prime_mismatch_and_a_non_refinement() {
    assert_eq!(
        OmegaRestriction::new(level(3, 1), level(5, 1)),
        Err(IwasawaRefusal::PrimeMismatch { left: 3, right: 5 })
    );
    assert_eq!(
        OmegaRestriction::new(level(3, 2), level(3, 1)),
        Err(IwasawaRefusal::NotARefinement { coarse: 2, fine: 1 })
    );
}

// -------------------------------------------------------------------------------------------
// 4. The finite ring (Z/p^e Z)[T]/(ω_n).
// -------------------------------------------------------------------------------------------

#[test]
fn the_finite_ring_refuses_its_declared_bounds() {
    // Degree 4096 is an accepted LEVEL but not an accepted RING: multiplication there is 16.7
    // million coefficient products.
    assert_eq!(
        FiniteLevelRing::new(level(2, 12), 2),
        Err(IwasawaRefusal::RingDegreeTooLarge {
            degree: 4096,
            bound: MAX_RING_DEGREE
        })
    );
    // Coefficient exponent 0 is the zero ring Z/1.
    assert_eq!(
        FiniteLevelRing::new(level(3, 1), 0),
        Err(IwasawaRefusal::ZeroRing)
    );
    assert_eq!(
        FiniteLevelRing::at_own_level(level(3, 0)),
        Err(IwasawaRefusal::ZeroRing),
        "R_0 = (Z/p^0)[T]/(ω_0) is the zero ring and is refused rather than returned"
    );
    assert_eq!(
        FiniteLevelRing::new(level(3, 1), MAX_COEFFICIENT_EXPONENT + 1),
        Err(IwasawaRefusal::CoefficientExponentTooLarge {
            exponent: MAX_COEFFICIENT_EXPONENT + 1,
            bound: MAX_COEFFICIENT_EXPONENT
        })
    );
}

#[test]
fn the_finite_ring_refuses_an_element_of_the_wrong_extent() {
    let small = FiniteLevelRing::new(level(3, 1), 2).expect("degree 3, modulus 9");
    let large = FiniteLevelRing::new(level(3, 2), 2).expect("degree 9, modulus 9");
    let foreign = large.one();
    assert_eq!(
        small.add(&small.one(), &foreign),
        Err(IwasawaRefusal::RingElementExtent {
            expected: 3,
            found: 9
        })
    );
    assert_eq!(
        small.mul(&foreign, &small.one()),
        Err(IwasawaRefusal::RingElementExtent {
            expected: 3,
            found: 9
        })
    );
    assert_eq!(
        small.pow(&foreign, 2),
        Err(IwasawaRefusal::RingElementExtent {
            expected: 3,
            found: 9
        })
    );
    assert!(!small.carries(&foreign));
    assert!(small.carries(&small.one()));
    // The exponent of `pow` is a caller-declared loop count, so it is bounded before the loop runs.
    assert_eq!(
        small.pow(&small.one(), MAX_RING_POWER + 1),
        Err(IwasawaRefusal::RingPowerTooLarge {
            exponent: MAX_RING_POWER + 1,
            bound: MAX_RING_POWER
        }),
        "the bound is checked BEFORE the element, so no multiplication is performed"
    );
    assert!(small.pow(&small.one(), MAX_RING_POWER).is_ok());
}

#[test]
fn the_finite_ring_multiplies_and_reduces_exactly() {
    // R_1 = (Z/3)[T]/(ω_1) at p = 3, with ω_1 = T^3 + 3T^2 + 3T. The task statement's R_n takes
    // the coefficient exponent equal to the level, so the coefficient ring here is Z/3.
    let ring = FiniteLevelRing::at_own_level(level(3, 1)).expect("R_1 exists");
    assert_eq!(ring.degree(), 3);
    assert_eq!(ring.coefficient_exponent(), 1);
    assert_eq!(ring.modulus(), &big(3));
    assert_eq!(ring.level(), &level(3, 1));

    // T^3 ≡ -3T^2 - 3T ≡ 0 (mod 3), so T^3 vanishes in (Z/3)[T]/(ω_1).
    assert!(
        ring.reduce(&ints(&[0, 0, 0, 1])).is_zero(),
        "T^3 = -3T^2 - 3T ≡ 0 mod 3"
    );
    // (1+T)^(p^n) - 1 = ω_n = 0 in the ring, so (1+T)^3 = 1.
    let one_plus_t = ring.reduce(&ints(&[1, 1]));
    assert_eq!(
        ring.pow(&one_plus_t, 3).expect("same ring"),
        ring.one(),
        "(1+T)^(p^n) = 1 in (Z/p^e)[T]/(ω_n)"
    );

    // At a coefficient exponent where the reduction is visible rather than zero.
    let wide = FiniteLevelRing::new(level(3, 1), 2).expect("modulus 9");
    let t = wide.reduce(&ints(&[0, 1]));
    let t_squared = wide.mul(&t, &t).expect("same ring");
    assert_eq!(t_squared.coefficients(), &[big(0), big(0), big(1)]);
    let t_cubed = wide.mul(&t_squared, &t).expect("same ring");
    // T^3 ≡ -3T - 3T^2 ≡ 6T + 6T^2 (mod 9).
    assert_eq!(t_cubed.coefficients(), &[big(0), big(6), big(6)]);
    assert_eq!(t_cubed, wide.pow(&t, 3).expect("same ring"));
    assert_eq!(
        wide.add(&wide.one(), &wide.reduce(&ints(&[8])))
            .expect("same ring")
            .coefficients(),
        &[big(0), big(0), big(0)],
        "1 + 8 = 0 in Z/9"
    );
    // Reduction is total on an input of any degree.
    assert_eq!(
        wide.reduce(&ints(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]))
            .coefficients()
            .len(),
        3
    );
    assert_eq!(wide.zero().coefficients(), &[big(0), big(0), big(0)]);
    assert!(wide.zero().is_zero());
}

// -------------------------------------------------------------------------------------------
// 5. Presentations, their refusals, and the relation-matrix area bound.
// -------------------------------------------------------------------------------------------

#[test]
fn the_presentation_constructor_refuses_its_declared_bounds() {
    assert_eq!(
        LambdaPresentation::new(Vec::new()),
        Err(IwasawaRefusal::EmptyPresentation)
    );
    assert_eq!(
        LambdaPresentation::new(vec![ints(&[1]); MAX_GENERATORS + 1]),
        Err(IwasawaRefusal::TooManyGenerators {
            count: MAX_GENERATORS + 1,
            bound: MAX_GENERATORS
        })
    );
    assert_eq!(
        LambdaPresentation::new(vec![ints(&[1]), Vec::new()]),
        Err(IwasawaRefusal::ZeroGenerator { index: 1 })
    );
    assert_eq!(
        LambdaPresentation::new(vec![ints(&[1]), ints(&[0, 0, 0])]),
        Err(IwasawaRefusal::ZeroGenerator { index: 1 }),
        "a vector of zeros is the zero polynomial however it is spelled"
    );
    let mut long = vec![BigInt::zero(); MAX_GENERATOR_DEGREE + 1];
    long.push(BigInt::one());
    assert_eq!(
        LambdaPresentation::new(vec![long]),
        Err(IwasawaRefusal::GeneratorDegreeTooLarge {
            index: 0,
            degree: MAX_GENERATOR_DEGREE + 1,
            bound: MAX_GENERATOR_DEGREE
        })
    );
    // An accepted presentation stores the TRIMMED generators.
    let trimmed = LambdaPresentation::principal(ints(&[-3, 1, 0, 0])).expect("degree 1");
    assert_eq!(trimmed.generators(), &[ints(&[-3, 1])]);
    assert_eq!(trimmed.generator_count(), 1);
}

#[test]
fn the_relation_matrix_area_bound_fires_before_anything_is_allocated() {
    // Level 12 at p = 2 has degree 4096, which IwasawaLevel accepts. One generator then wants a
    // 4096 × 4096 matrix of 16,777,216 BigInt entries. The area check refuses it, and it refuses
    // before ω_12 (4097 binomial coefficients) is built and before any matrix is allocated.
    let single = presented(&[&[-2, 1]]);
    let expected = IwasawaRefusal::RelationMatrixTooLarge {
        rows: 4096,
        columns: 4096,
        area: 16_777_216,
        bound: MAX_RELATION_MATRIX_AREA,
    };
    assert_eq!(single.relation_matrix(&level(2, 12)), Err(expected.clone()));
    assert_eq!(single.specialize(&level(2, 12)), Err(expected));
    // Two generators at degree 512 already exceed the bound: 1024 × 512 = 524,288.
    let two = presented(&[&[-2, 1], &[0, 1]]);
    assert_eq!(
        two.relation_matrix(&level(2, 9)),
        Err(IwasawaRefusal::RelationMatrixTooLarge {
            rows: 1024,
            columns: 512,
            area: 524_288,
            bound: MAX_RELATION_MATRIX_AREA
        })
    );
    // The largest area this module's own tests use is tiny by comparison.
    let matrix = two
        .relation_matrix(&level(3, 3))
        .expect("54 × 27 = 1458 is well inside the bound");
    assert_eq!((matrix.rows(), matrix.columns()), (54, 27));
}

#[test]
fn the_relation_matrix_is_the_shifted_generator_reduced_mod_omega() {
    // p = 3, n = 1: basis 1, T, T^2; ω_1 = T^3 + 3T^2 + 3T. Generator f = T - 3.
    // Rows: f = -3 + T; T·f = -3T + T^2; T^2·f = T^3 - 3T^2 = (-3T - 3T^2) - 3T^2 = -3T - 6T^2.
    let matrix = presented(&[&[-3, 1]])
        .relation_matrix(&level(3, 1))
        .expect("3 × 3 is inside the bound");
    assert_eq!((matrix.rows(), matrix.columns()), (3, 3));
    let row = |index: usize| -> Vec<BigInt> {
        (0..matrix.columns())
            .map(|column| matrix.at(index, column).clone())
            .collect()
    };
    assert_eq!(row(0), ints(&[-3, 1, 0]));
    assert_eq!(row(1), ints(&[0, -3, 1]));
    assert_eq!(row(2), ints(&[0, -3, -6]));
}

#[test]
fn the_specialization_is_refused_when_it_is_not_finite() {
    // Λ/(T) ≅ Z_p, which is not finite. The relation matrix is rank deficient at every level.
    let along_t = presented(&[&[0, 1]]);
    for (n, basis_dimension, rank) in [(0_u32, 1_usize, 0_usize), (1, 3, 2), (2, 9, 8)] {
        assert_eq!(
            along_t.specialize(&level(3, n)),
            Err(IwasawaRefusal::NotFinite {
                basis_dimension,
                rank,
                prime: 3,
                level: n
            }),
            "Λ/(T) leaves a free Z_p-summand at level {n}"
        );
    }
}

// -------------------------------------------------------------------------------------------
// 6. Finite specializations: the measured groups.
// -------------------------------------------------------------------------------------------

#[test]
fn lambda_over_p_specializes_to_the_truncated_polynomial_ring() {
    // Λ/(p) = F_p[[T]], and (1+T)^(p^n) - 1 ≡ T^(p^n) mod p, so M/ω_n M = F_p[T]/(T^(p^n)) is
    // elementary abelian of rank p^n and order p^(p^n).
    let over_p = presented(&[&[3]]);
    for (n, exponent) in [(0_u32, 1_u32), (1, 3), (2, 9), (3, 27)] {
        let specialization = over_p
            .specialize(&level(3, n))
            .expect("Λ/(p) is finite at every level");
        assert_eq!(specialization.smith_rank(), specialization.basis_dimension());
        assert_eq!(specialization.basis_dimension(), level(3, n).degree());
        assert_eq!(specialization.growth_exponent(), u64::from(exponent));
        assert_eq!(specialization.order(), &big(3).pow(exponent));
        assert!(specialization.is_p_primary());
        assert_eq!(specialization.prime_to_p_part(), &BigUint::one());
        assert_eq!(
            specialization.p_primary_type(),
            vec![1_u32; specialization.basis_dimension()].as_slice(),
            "every cyclic summand is Z/p"
        );
        assert_eq!(
            specialization.p_valuations(),
            vec![1_u32; specialization.basis_dimension()].as_slice()
        );
        for factor in specialization.invariant_factors() {
            assert_eq!(factor, &BigInt::from(3));
        }
        assert_eq!(specialization.level(), &level(3, n));
    }
}

#[test]
fn the_prime_to_p_part_is_reported_and_never_dropped_in_silence() {
    // Λ/(T - p) ≅ Z_p, so M/ω_n M = Z/ω_n(p) = Z/((1+p)^(p^n) - 1). At p = 3, n = 1 that integer
    // is 4^3 - 1 = 63 = 3^2 · 7: the Z_p-module is Z/9 and the cofactor 7 is real.
    let over_t_minus_p = presented(&[&[-3, 1]]);
    for (n, integral, exponent, cofactor) in [
        (0_u32, 3_u64, 1_u32, 1_u64),
        (1, 63, 2, 7),
        (2, 262_143, 3, 9_709),
    ] {
        let specialization = over_t_minus_p.specialize(&level(3, n)).expect("finite");
        assert_eq!(
            specialization.invariant_factors(),
            &[BigInt::from(integral)],
            "the Z-cokernel at level {n} is cyclic of order {integral}"
        );
        assert_eq!(specialization.integral_order(), &big(integral));
        assert_eq!(specialization.growth_exponent(), u64::from(exponent));
        assert_eq!(specialization.order(), &big(3).pow(exponent));
        assert_eq!(specialization.prime_to_p_part(), &big(cofactor));
        assert_eq!(specialization.is_p_primary(), cofactor == 1);
        assert_eq!(specialization.p_primary_type(), &[exponent]);
        assert_eq!(specialization.p_valuations(), &[exponent]);
        assert_eq!(
            specialization.integral_order(),
            &(specialization.order() * specialization.prime_to_p_part()),
            "the two orders and the cofactor are exactly consistent"
        );
    }
}

#[test]
fn a_unit_generator_gives_the_zero_module_and_a_unit_face() {
    let unit = presented(&[&[1]]);
    for n in 0..3 {
        let specialization = unit.specialize(&level(3, n)).expect("finite");
        assert!(specialization.is_trivial());
        assert_eq!(specialization.order(), &BigUint::one());
        assert_eq!(specialization.growth_exponent(), 0);
        assert!(specialization.invariant_factors().is_empty());
    }
    assert!(unit.characteristic_face(3).is_unit());

    // T - 1 is a unit of Z_p[[T]] because its constant term is a unit, so Λ/(T-1) = 0 as a
    // Z_p-module — while the Z-cokernel is Z/(2^(p^n) - 1), which is not trivial.
    let shifted = presented(&[&[-1, 1]]);
    let specialization = shifted.specialize(&level(3, 1)).expect("finite");
    assert_eq!(specialization.order(), &BigUint::one());
    assert_eq!(specialization.integral_order(), &big(7));
    assert!(!specialization.is_p_primary());
    assert!(specialization.p_primary_type().is_empty());
    assert_eq!(specialization.p_valuations(), &[0_u32]);
}

#[test]
fn the_smith_invariants_do_not_move_with_the_pivot_rule() {
    // A gauge check on the relation matrix, using the wave-1 owner's own three rules. The matrix
    // is small on purpose: `FirstNonzero` is the rule `rebase_invariants` measured as pathological.
    let matrix = presented(&[&[9, -6, 1]])
        .relation_matrix(&level(3, 1))
        .expect("3 × 3 is inside the bound");
    let reference = smith_normal_form(&matrix, PivotRule::SmallestMagnitude);
    for rule in PivotRule::ALL {
        let form = smith_normal_form(&matrix, rule);
        assert_eq!(
            form.torsion(),
            reference.torsion(),
            "rule {rule:?} moved the factors"
        );
        assert_eq!(form.rank(), reference.rank());
        assert!(form.divisibility_holds());
    }
    assert_eq!(reference.rank(), 3);
    assert_eq!(reference.torsion(), ints(&[3, 1323]));
}

// -------------------------------------------------------------------------------------------
// 7. The two counterexample pairs.
// -------------------------------------------------------------------------------------------

#[test]
fn the_characteristic_face_does_not_determine_the_module() {
    // f = T - p, so Λ/(f) ≅ Z_p. M1 = Λ/(f^2) and M2 = Λ/(f) ⊕ Λ/(f) carry the SAME
    // characteristic ideal (f^2) — for M2 by multiplicativity of the characteristic ideal over a
    // direct sum, which is classical and cited, and which this test evaluates by multiplying the
    // two summands' generators. At every level they have the same order and different finite types.
    let f = ints(&[-3, 1]);
    let f_squared = poly_mul(&f, &f);
    assert_eq!(f_squared, ints(&[9, -6, 1]));

    let m1 = LambdaPresentation::principal(f_squared.clone()).expect("degree 2");
    let summand = LambdaPresentation::principal(f).expect("degree 1");

    assert_eq!(
        m1.characteristic_face(3).principal_generator(),
        Some(f_squared.as_slice()),
        "M1's characteristic ideal is (f^2)"
    );
    let summand_face = summand.characteristic_face(3);
    let summand_generator = summand_face
        .principal_generator()
        .expect("a one-generator presentation has a principal face");
    assert_eq!(
        poly_mul(summand_generator, summand_generator),
        f_squared,
        "M2's characteristic ideal is (f)·(f) = (f^2), the same ideal"
    );
    assert!(!m1.characteristic_face(3).is_unit());

    // The MEASURED types. These came out of the Smith normal form; nothing here was asserted into
    // being. M1 → [n, n+2] (the zero exponent dropped at n = 0); M2 → [n+1, n+1].
    let expected: [(u32, &[u32], &[u32], u32); 3] = [
        (0, &[2], &[1, 1], 2),
        (1, &[1, 3], &[2, 2], 4),
        (2, &[2, 4], &[3, 3], 6),
    ];
    for (n, type_one, type_two, exponent) in expected {
        let chart = level(3, n);
        let left = m1.specialize(&chart).expect("finite");
        let right_summand = summand.specialize(&chart).expect("finite");
        let right =
            SpecializationType::direct_sum(&[right_summand.p_type(), right_summand.p_type()])
                .expect("both summands are at the same level");

        assert_eq!(
            left.order(),
            right.order(),
            "the orders must agree at n = {n}"
        );
        assert_eq!(left.order(), &big(3).pow(exponent));
        assert_eq!(left.growth_exponent(), u64::from(exponent));
        assert_eq!(right.growth_exponent(), u64::from(exponent));
        assert_eq!(right.level(), &chart);

        assert_eq!(left.p_primary_type(), type_one, "M1 type at n = {n}");
        assert_eq!(right.p_primary_type(), type_two, "M2 type at n = {n}");
        assert_ne!(
            left.p_primary_type(),
            right.p_primary_type(),
            "the two modules are non-isomorphic at n = {n} despite the same characteristic ideal"
        );
    }
}

#[test]
fn the_measured_m1_type_is_not_the_cyclic_one_a_guess_would_give() {
    // A plausible guess is M1 ≅ Z/p^(2(n+1)), cyclic. It is wrong for n ≥ 1: the elementary
    // divisors of [[a, b], [0, a]] with a = ω_n(p) and b = ω_n'(p) are gcd(a, b) and a²/gcd(a, b),
    // and v_p(a) = n+1 while v_p(b) = n, so the split is (n, n+2) and never (0, 2n+2).
    let m1 = presented(&[&[9, -6, 1]]);
    for n in 1..3_u32 {
        let specialization = m1.specialize(&level(3, n)).expect("finite");
        assert_ne!(
            specialization.p_primary_type(),
            vec![2 * (n + 1)].as_slice(),
            "M1 is NOT cyclic of order p^(2(n+1)) at n = {n}"
        );
        assert_eq!(specialization.p_primary_type(), &[n, n + 2]);
        assert_eq!(
            specialization.growth_exponent(),
            u64::from(2 * (n + 1)),
            "the ORDER is still p^(2(n+1)); only the decomposition differs"
        );
    }
    // At n = 0 the module happens to be cyclic, and (n, n+2) = (0, 2) agrees once the zero
    // exponent is dropped.
    assert_eq!(
        m1.specialize(&level(3, 0)).expect("finite").p_primary_type(),
        &[2]
    );
    // The Z-cokernels at n = 1: d_1 = 3, d_2 = 1323 = 3^3 · 7^2.
    let at_one = m1.specialize(&level(3, 1)).expect("finite");
    assert_eq!(at_one.invariant_factors(), &ints(&[3, 1323])[..]);
    assert_eq!(at_one.p_valuations(), &[1_u32, 3]);
    assert_eq!(at_one.prime_to_p_part(), &big(49));
}

#[test]
fn the_pseudo_null_residue_is_invisible_to_the_face() {
    // M = Λ/(p, T) ≅ F_p. Its characteristic ideal is the unit ideal — the characteristic ideal of
    // the ZERO module — while M itself is finite of order exactly p at every level and nonzero.
    let m = presented(&[&[3], &[0, 1]]);
    let face = m.characteristic_face(3);
    assert_eq!(face, CharacteristicFace::Unit);
    assert!(
        face.is_unit(),
        "the codimension-one datum is trivial: it cannot see this module at all"
    );
    assert!(face.principal_generator().is_none());
    for n in 0..4_u32 {
        let specialization = m.specialize(&level(3, n)).expect("finite at every level");
        assert_eq!(
            specialization.order(),
            &big(3),
            "|M/ω_n M| = p at level {n}"
        );
        assert!(
            !specialization.is_trivial(),
            "the module is NOT zero at level {n}"
        );
        assert_eq!(specialization.p_primary_type(), &[1_u32]);
        assert_eq!(specialization.invariant_factors(), &[BigInt::from(3)]);
        assert!(specialization.is_p_primary());
        assert_eq!(specialization.growth_exponent(), 1);
    }
    // The same at another prime, so the order-p answer is not an artefact of p = 3.
    let m5 = presented(&[&[5], &[0, 1]]);
    assert_eq!(m5.characteristic_face(5), CharacteristicFace::Unit);
    for n in 0..3_u32 {
        assert_eq!(
            m5.specialize(&level(5, n)).expect("finite").order(),
            &big(5)
        );
    }
}

#[test]
fn a_shared_factor_leaves_the_characteristic_face_undetermined() {
    // (T-3)(T-9) and (T-3)·T share the factor T-3, so the ideal has height one and this owner does
    // not guess: it returns the common factor it found.
    match presented(&[&[27, -12, 1], &[0, -3, 1]]).characteristic_face(3) {
        CharacteristicFace::Undetermined {
            common_factor,
            prime_is_common,
        } => {
            assert_eq!(common_factor, ints(&[-3, 1]), "the gcd in Q[T] is T - 3");
            assert!(!prime_is_common);
        }
        other => panic!("expected an undetermined face, got {other:?}"),
    }
    // Two generators both divisible by p: p itself is the common factor in Λ.
    match presented(&[&[3], &[0, 3]]).characteristic_face(3) {
        CharacteristicFace::Undetermined {
            prime_is_common, ..
        } => assert!(prime_is_common),
        other => panic!("expected an undetermined face, got {other:?}"),
    }
    // (p, T) has gcd 1 in Q[T] and is not uniformly divisible by p, so it IS the unit face.
    assert_eq!(
        presented(&[&[3], &[0, 1]]).characteristic_face(3),
        CharacteristicFace::Unit
    );
}

#[test]
fn the_direct_sum_refuses_a_level_mismatch_and_an_empty_list() {
    let summand = presented(&[&[-3, 1]]);
    let at_one = summand.specialize(&level(3, 1)).expect("finite").p_type();
    let at_two = summand.specialize(&level(3, 2)).expect("finite").p_type();
    assert_eq!(
        SpecializationType::direct_sum(&[at_one.clone(), at_two]),
        Err(IwasawaRefusal::LevelMismatch { left: 1, right: 2 })
    );
    assert_eq!(
        SpecializationType::direct_sum(&[]),
        Err(IwasawaRefusal::EmptyDirectSum)
    );
    // A one-element sum is the summand itself.
    assert_eq!(
        SpecializationType::direct_sum(std::slice::from_ref(&at_one)).expect("one summand"),
        at_one
    );
    // A three-fold sum concatenates three copies.
    let triple = SpecializationType::direct_sum(&[at_one.clone(), at_one.clone(), at_one])
        .expect("same level");
    assert_eq!(triple.p_primary_type(), &[2_u32, 2, 2]);
    assert_eq!(triple.order(), &big(3).pow(6));
    assert_eq!(triple.growth_exponent(), 6);
}

// -------------------------------------------------------------------------------------------
// 8. The growth exponents μ, λ, ν.
// -------------------------------------------------------------------------------------------

fn assert_fit(
    generators: &[&[i64]],
    prime: u64,
    base: u32,
    mu: i64,
    lambda: i64,
    nu: i64,
) -> GrowthFit {
    let fit = fit_and_verify_growth(&presented(generators), prime, base)
        .unwrap_or_else(|refusal| panic!("fit failed for {generators:?}: {refusal}"));
    assert_eq!(
        fit.exponents().mu(),
        &BigInt::from(mu),
        "μ for {generators:?}"
    );
    assert_eq!(
        fit.exponents().lambda(),
        &BigInt::from(lambda),
        "λ for {generators:?}"
    );
    assert_eq!(
        fit.exponents().nu(),
        &BigInt::from(nu),
        "ν for {generators:?}"
    );
    assert!(fit.exponents().is_iwasawa_admissible());
    assert_eq!(fit.exponents().prime(), prime);
    assert_eq!(fit.exponents().base_level(), base);
    assert_eq!(fit.fitted_from().len(), 3);
    assert_eq!(fit.verified_at().0, base + 3);
    fit
}

#[test]
fn the_growth_exponents_of_t_minus_p_are_mu_zero_lambda_one() {
    let fit = assert_fit(&[&[-3, 1]], 3, 0, 0, 1, 1);
    assert_eq!(
        fit.fitted_from(),
        &[(0, 1), (1, 2), (2, 3)],
        "the measured e_n, which is v_p((1+p)^(p^n) - 1) = n + 1"
    );
    assert_eq!(fit.verified_at(), (3, 4));
}

#[test]
fn the_growth_exponents_of_p_are_mu_one_lambda_zero() {
    let fit = assert_fit(&[&[3]], 3, 0, 1, 0, 0);
    assert_eq!(fit.fitted_from(), &[(0, 1), (1, 3), (2, 9)]);
    assert_eq!(fit.verified_at(), (3, 27));
}

#[test]
fn the_growth_exponents_of_p_squared_are_mu_two() {
    let fit = assert_fit(&[&[9]], 3, 0, 2, 0, 0);
    assert_eq!(fit.fitted_from(), &[(0, 2), (1, 6), (2, 18)]);
    assert_eq!(fit.verified_at(), (3, 54));
}

#[test]
fn a_degree_two_distinguished_generator_has_lambda_two() {
    // f = (T - p)(T - p^2) = T^2 - (p + p^2)T + p^3, distinguished of degree 2.
    assert_eq!(
        poly_mul(&ints(&[-3, 1]), &ints(&[-9, 1])),
        ints(&[27, -12, 1])
    );
    let fit = assert_fit(&[&[27, -12, 1]], 3, 0, 0, 2, 3);
    assert_eq!(
        fit.fitted_from(),
        &[(0, 3), (1, 5), (2, 7)],
        "e_n = 2n + 3 = v_p(ω_n(p)) + v_p(ω_n(p^2)) = (n+1) + (n+2)"
    );
    assert_eq!(fit.verified_at(), (3, 9));
}

#[test]
fn the_pseudo_null_module_has_zero_mu_and_zero_lambda() {
    let fit = assert_fit(&[&[3], &[0, 1]], 3, 0, 0, 0, 1);
    assert_eq!(
        fit.fitted_from(),
        &[(0, 1), (1, 1), (2, 1)],
        "a pseudo-null module's order does not grow"
    );
    assert_eq!(fit.verified_at(), (3, 1));
}

#[test]
fn the_shape_does_not_hold_below_its_own_n_zero() {
    // Iwasawa's theorem asserts the shape for n ≥ n₀. At p = 2 with f = T - 2 the measured
    // exponents are e = [1, 3, 4, 5, 6]: v_2(3^(2^n) - 1) is 1 at n = 0 and n + 3 above it. Fitting
    // from base level 0 therefore returns μ = -1 and fails its own verification; fitting from base
    // level 1 returns (0, 1, 2) and verifies at level 4.
    let over_t_minus_two = presented(&[&[-2, 1]]);
    assert_eq!(
        measure_growth(&over_t_minus_two, 2, &[0, 1, 2, 3, 4]).expect("all finite"),
        vec![(0, 1), (1, 3), (2, 4), (3, 5), (4, 6)]
    );

    let below = GrowthExponents::fit(2, 0, [1, 3, 4]).expect("the system has an exact solution");
    assert_eq!(below.mu(), &BigInt::from(-1));
    assert_eq!(below.lambda(), &BigInt::from(3));
    assert_eq!(below.nu(), &BigInt::from(2));
    assert!(
        !below.is_iwasawa_admissible(),
        "a negative μ says these three levels lie below this module's n₀, not that the theorem fails"
    );
    assert_eq!(
        fit_and_verify_growth(&over_t_minus_two, 2, 0),
        Err(IwasawaRefusal::GrowthFitDisagrees {
            level: 3,
            predicted: BigInt::from(3),
            measured: 5,
            exponents: Box::new(below),
        }),
        "the verification level is what catches it; nothing is rounded into agreement"
    );

    let above = assert_fit(&[&[-2, 1]], 2, 1, 0, 1, 2);
    assert_eq!(above.fitted_from(), &[(1, 3), (2, 4), (3, 5)]);
    assert_eq!(above.verified_at(), (4, 6));
}

#[test]
fn a_growth_fit_that_does_not_divide_exactly_is_refused() {
    // e = [0, 0, 1] at p = 3 from base 0: the second difference is 1 and the divisor is
    // p^0 (p-1)^2 = 4, which does not divide it.
    match GrowthExponents::fit(3, 0, [0, 0, 1]) {
        Err(IwasawaRefusal::NoExactGrowthFit {
            second_difference,
            divisor,
            prime,
            base_level,
            ..
        }) => {
            assert_eq!(second_difference, BigInt::one());
            assert_eq!(divisor, BigInt::from(4));
            assert_eq!(prime, 3);
            assert_eq!(base_level, 0);
        }
        other => panic!("expected NoExactGrowthFit, got {other:?}"),
    }
}

#[test]
fn the_fit_takes_differences_over_the_integers_and_never_underflows() {
    // A decreasing exponent sequence is not a real Iwasawa module, but the solver must not
    // underflow on it: the differences are taken over BigInt and not over u64.
    let decreasing = GrowthExponents::fit(3, 0, [10, 6, 2]).expect("an exact solution exists");
    assert_eq!(decreasing.mu(), &BigInt::zero());
    assert_eq!(decreasing.lambda(), &BigInt::from(-4));
    assert_eq!(decreasing.nu(), &BigInt::from(10));
    assert!(!decreasing.is_iwasawa_admissible());
}

#[test]
fn the_fit_refuses_a_base_level_that_is_not_a_level() {
    // `p^base_level` is never built from the raw u32: (prime, base_level) goes through
    // IwasawaLevel::new first, so a four-billion base level is refused before any BigInt power.
    assert_eq!(
        GrowthExponents::fit(3, 1_000_000, [1, 2, 3]),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 3,
            level: 1_000_000,
            bound: MAX_DEGREE
        })
    );
    assert_eq!(
        GrowthExponents::fit(4, 0, [1, 2, 3]),
        Err(IwasawaRefusal::NotPrime { prime: 4 })
    );
}

#[test]
fn prediction_refuses_a_foreign_prime() {
    let fit = GrowthExponents::fit(3, 0, [1, 2, 3]).expect("exact");
    assert_eq!(
        fit.predict(&level(5, 1)),
        Err(IwasawaRefusal::PrimeMismatch { left: 3, right: 5 })
    );
    assert_eq!(
        fit.predict(&level(3, 3)).expect("same prime"),
        BigInt::from(4)
    );
}

#[test]
fn measure_growth_propagates_the_level_refusal() {
    let over_t_minus_p = presented(&[&[-3, 1]]);
    assert_eq!(
        measure_growth(&over_t_minus_p, 3, &[0, 8]),
        Err(IwasawaRefusal::DegreeTooLarge {
            prime: 3,
            level: 8,
            bound: MAX_DEGREE
        })
    );
    assert_eq!(
        measure_growth(&over_t_minus_p, 4, &[0]),
        Err(IwasawaRefusal::NotPrime { prime: 4 })
    );
}

// -------------------------------------------------------------------------------------------
// 9. The private exact polynomial arithmetic, checked directly.
// -------------------------------------------------------------------------------------------

#[test]
fn monic_division_is_total_and_exact() {
    let divisor = omega(&level(3, 1)); // T^3 + 3T^2 + 3T
    let cases: Vec<Vec<BigInt>> = vec![
        Vec::new(),
        ints(&[1]),
        ints(&[0, 0, 0, 1]),
        ints(&[5, -4, 3, -2, 1]),
        ints(&[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
        ints(&[-7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13]),
        divisor.clone(),
    ];
    for dividend in &cases {
        let (quotient, remainder) = poly_div_rem_monic(dividend, &divisor);
        assert_eq!(
            poly_add(&poly_mul(&divisor, &quotient), &remainder),
            trim(dividend.clone()),
            "a = ω·q + r failed on {dividend:?}"
        );
        assert!(
            degree_of(&remainder).is_none_or(|degree| degree < 3),
            "the remainder must have degree below deg ω_1 = 3"
        );
    }
    // ω_1 divides itself with quotient 1 and no remainder.
    let (quotient, remainder) = poly_div_rem_monic(&divisor, &divisor);
    assert_eq!(quotient, ints(&[1]));
    assert!(remainder.is_empty());
}

#[test]
fn the_rational_gcd_is_the_primitive_common_factor() {
    // (T-3)(T-9) and (T-3)(T-1) share exactly T - 3.
    let left = poly_mul(&ints(&[-3, 1]), &ints(&[-9, 1]));
    let right = poly_mul(&ints(&[-3, 1]), &ints(&[-1, 1]));
    assert_eq!(rational_gcd(&left, &right), ints(&[-3, 1]));
    // Coprime polynomials give the constant 1.
    assert_eq!(rational_gcd(&ints(&[-3, 1]), &ints(&[-9, 1])), ints(&[1]));
    // A constant and a polynomial: the gcd in Q[T] is 1, which is what the height-two criterion
    // needs — a common factor of p is a separate, integral test.
    assert_eq!(rational_gcd(&ints(&[3]), &ints(&[0, 1])), ints(&[1]));
    // The result is primitive with a positive leading coefficient, whatever the inputs' contents.
    assert_eq!(rational_gcd(&ints(&[3, -1]), &ints(&[6, -2])), ints(&[-3, 1]));
    assert_eq!(rational_gcd(&ints(&[6, -2]), &ints(&[9, -3])), ints(&[-3, 1]));
}

#[test]
fn the_p_valuation_splits_a_factor_exactly() {
    assert_eq!(p_valuation(&big(63), &big(3)), (2, big(7)));
    assert_eq!(p_valuation(&big(1), &big(3)), (0, big(1)));
    assert_eq!(p_valuation(&big(81), &big(3)), (4, big(1)));
    assert_eq!(p_valuation(&BigUint::zero(), &big(3)), (0, BigUint::zero()));
}

// -------------------------------------------------------------------------------------------
// 10. No float anywhere.
// -------------------------------------------------------------------------------------------

#[test]
fn the_module_source_contains_no_floating_point_type() {
    // A standing project rule, checked against this owner's own source rather than asserted.
    let source = include_str!("../iwasawa_tower.rs");
    for forbidden in ["f32", "f64"] {
        assert!(
            !source.contains(forbidden),
            "the machinery must carry no {forbidden}"
        );
    }
}

#[test]
fn the_not_finite_display_is_total_even_when_the_rank_exceeds_the_basis() {
    // `Display` must be total on every value of the type, and `IwasawaRefusal` is a public enum a
    // caller can construct. The free rank it reports saturates: a `rank > basis_dimension` value
    // formats as a free rank of zero instead of underflowing a `usize` inside a formatter.
    let genuine = IwasawaRefusal::NotFinite {
        basis_dimension: 9,
        rank: 8,
        prime: 3,
        level: 2,
    };
    assert!(
        genuine.to_string().contains("free Z_p-summand of rank 1"),
        "{genuine}"
    );

    let inverted = IwasawaRefusal::NotFinite {
        basis_dimension: 2,
        rank: 7,
        prime: 3,
        level: 1,
    };
    let rendered = inverted.to_string();
    assert!(
        rendered.contains("free Z_p-summand of rank 0"),
        "a rank above the basis dimension saturates to zero rather than panicking: {rendered}"
    );
    assert!(rendered.contains("relation rank 7"));
    assert!(rendered.contains("basis dimension 2"));

    // The extreme of the same shape.
    let extreme = IwasawaRefusal::NotFinite {
        basis_dimension: 0,
        rank: usize::MAX,
        prime: 2,
        level: 0,
    };
    assert!(extreme.to_string().contains("free Z_p-summand of rank 0"));
}

#[test]
fn the_module_body_holds_exactly_the_expects_its_header_accounts_for() {
    // The header names every `expect` and `unwrap_or` in the module body and says why each cannot
    // fire. This counts them, so the header cannot drift from the source.
    let source = include_str!("../iwasawa_tower.rs");
    let body = source
        .split("#[cfg(test)]")
        .next()
        .expect("the module body precedes its test declaration");
    assert_eq!(
        body.matches("expect(").count(),
        4,
        "the header accounts for four internal expects"
    );
    assert_eq!(
        body.matches("unwrap_or(").count(),
        2,
        "and for two unwrap_or fallbacks"
    );
    assert_eq!(
        body.matches(".unwrap()").count(),
        0,
        "and for no unwrap at all"
    );
    for named in [
        "poly_div_rem_monic",
        "FiniteLevelRing::reduce",
        "LambdaPresentation::specialize",
        "fit_and_verify_growth",
        "check_distinguished",
        "IwasawaTower::new",
    ] {
        assert!(
            body.contains(named),
            "the header accounts for an occurrence in {named}, which is not in the module"
        );
    }
}

// -------------------------------------------------------------------------------------------
// 11. The citation table.
// -------------------------------------------------------------------------------------------

/// The Lean names this module's header correspondence table cites, parsed from the module's own
/// source exactly as an exterior citation test parses it: rows `//! | ` + backticked Lean names +
/// `| ` + the Rust owner, Lean names in the first column.
fn cited_lean_names(module_source: &str) -> Vec<String> {
    module_source
        .lines()
        .map(str::trim_start)
        .filter(|line| line.starts_with("//! | `"))
        .filter_map(|line| line.strip_prefix("//! |"))
        .filter_map(|row| row.split('|').next())
        .flat_map(|cell| {
            cell.split('`')
                .skip(1)
                .step_by(2)
                .map(|name| name.trim().to_owned())
                .collect::<Vec<String>>()
        })
        .collect()
}

/// Whether the Lean owner declares a cited name. Lean writes a declaration unqualified inside its
/// own `namespace`, so a qualified citation such as `IwasawaTower.omegaPoly` is resolved by its
/// final segment; structure fields and inductive constructors are declarations too.
fn lean_declares(owner: &str, cited: &str) -> bool {
    let segment = cited.rsplit('.').next().unwrap_or(cited);
    owner.lines().any(|line| {
        let line = line.trim_start();
        let head = [
            "theorem ",
            "lemma ",
            "def ",
            "noncomputable def ",
            "structure ",
            "inductive ",
            "abbrev ",
            "class ",
            "instance ",
            "| ",
        ]
        .iter()
        .find_map(|keyword| line.strip_prefix(keyword))
        .unwrap_or(line);
        [cited, segment].iter().any(|name| {
            head.strip_prefix(*name).is_some_and(|rest| {
                !rest.starts_with(|character: char| {
                    character.is_alphanumeric() || character == '_' || character == '\''
                })
            })
        })
    })
}

#[test]
fn every_lean_name_the_header_cites_is_declared_by_the_lean_owner() {
    let module = include_str!("../iwasawa_tower.rs");
    let owner = include_str!(
        "../../../../formal/elementary-holonics/ElementaryHolonics/Foundation/IwasawaTower.lean"
    );
    let names = cited_lean_names(module);
    assert!(
        names.len() >= 8,
        "the header's correspondence table went missing: {} names parsed",
        names.len()
    );
    for name in &names {
        assert!(
            lean_declares(owner, name),
            "Foundation/IwasawaTower.lean declares no `{name}`, so the header cites a name that \
             does not exist"
        );
    }
}
