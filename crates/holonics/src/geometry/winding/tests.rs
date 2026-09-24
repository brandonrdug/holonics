//! Exact checks mirroring the Lean theorems this module implements: `PhaseCarry`,
//! `PairResonance`/`Farey`, `GeneratorTraceFaces`/`LocalFactor`/`TraceSequence` and `CellHolonomy`.

use super::*;
use crate::geometry::{ScrewGenerator, SituatedScrew, cayley_rotation_z, integer, rat};

fn nat(value: u32) -> BigUint {
    BigUint::from(value)
}

// -- 1. phase, winding, carry ---------------------------------------------------------------

#[test]
fn phase_and_winding_reconstruct_the_integer() {
    for modulus in 1u32..=7 {
        for value in 0u32..40 {
            let n = nat(modulus);
            let x = nat(value);
            let p = phase(&n, &x).expect("a positive modulus");
            let w = winding(&n, &x).expect("a positive modulus");
            assert_eq!(&p + &n * &w, x, "phase + n*winding must be x");
            assert!(p < n);
        }
    }
    assert_eq!(phase(&nat(0), &nat(3)), Err(WindingError::ZeroModulus));
    assert_eq!(winding(&nat(0), &nat(3)), Err(WindingError::ZeroModulus));
    assert_eq!(
        carry(&nat(0), &nat(3), &nat(1)),
        Err(WindingError::ZeroModulus)
    );
}

#[test]
fn the_carry_is_the_defect_of_the_windings_additivity() {
    for modulus in 1u32..=6 {
        let n = nat(modulus);
        for left in 0u32..20 {
            for right in 0u32..20 {
                let x = nat(left);
                let y = nat(right);
                let c = carry(&n, &x, &y).expect("a positive modulus");
                assert_eq!(
                    winding(&n, &(&x + &y)).expect("a positive modulus"),
                    winding(&n, &x).expect("a positive modulus")
                        + winding(&n, &y).expect("a positive modulus")
                        + &c
                );
                assert!(c <= BigUint::one(), "the carry is one turn or none");
            }
        }
    }
}

#[test]
fn the_carry_is_a_cocycle_over_an_exhaustive_small_range() {
    for modulus in 1u32..=5 {
        let n = nat(modulus);
        for a in 0u32..12 {
            for b in 0u32..12 {
                for c in 0u32..12 {
                    let (x, y, z) = (nat(a), nat(b), nat(c));
                    let left = carry(&n, &x, &y).expect("positive")
                        + carry(&n, &(&x + &y), &z).expect("positive");
                    let right = carry(&n, &y, &z).expect("positive")
                        + carry(&n, &x, &(&y + &z)).expect("positive");
                    assert_eq!(left, right, "bracketing must complete the same turns");
                }
            }
        }
    }
}

// -- odometer -------------------------------------------------------------------------------

#[test]
fn advance_equals_repeated_single_steps() {
    let radices = vec![nat(3), nat(4), nat(5)];
    let start = vec![nat(2), nat(3), nat(1)];
    for k in 0u32..60 {
        let mut jumped =
            Odometer::with_digits(radices.clone(), start.clone()).expect("a valid reading");
        jumped.advance(&nat(k));
        let mut stepped =
            Odometer::with_digits(radices.clone(), start.clone()).expect("a valid reading");
        for _ in 0..k {
            stepped.step();
        }
        assert_eq!(jumped, stepped, "advance({k}) must equal {k} single steps");
    }
}

#[test]
fn the_two_level_odometer_reads_the_phase_and_the_carried_winding() {
    let n = nat(7);
    for a in 0u32..7 {
        for b in 0u32..5 {
            for k in 0u32..50 {
                let mut odometer =
                    Odometer::with_digits(vec![n.clone(), nat(1000)], vec![nat(a), nat(b)])
                        .expect("a valid reading");
                odometer.advance(&nat(k));
                let advanced = nat(a + k);
                assert_eq!(
                    odometer.digits()[0],
                    phase(&n, &advanced).expect("positive")
                );
                assert_eq!(
                    odometer.digits()[1],
                    nat(b) + winding(&n, &advanced).expect("positive")
                );
                assert!(odometer.overflow_winding().is_zero());
            }
        }
    }
}

#[test]
fn the_digit_chart_is_faithful_and_refuses_a_degenerate_level() {
    let radices = vec![nat(2), nat(3), nat(5)];
    for value in 0u32..200 {
        let odometer = Odometer::from_value(radices.clone(), &nat(value)).expect("valid radices");
        assert_eq!(odometer.value(), nat(value));
        assert_eq!(odometer.levels(), 3);
    }
    assert_eq!(
        Odometer::new(vec![nat(3), nat(1)]),
        Err(WindingError::DegenerateRadix {
            level: 1,
            radix: nat(1)
        })
    );
    assert_eq!(
        Odometer::with_digits(vec![nat(3)], vec![nat(3)]),
        Err(WindingError::DigitOutOfRange {
            level: 0,
            digit: nat(3),
            radix: nat(3)
        })
    );
    assert!(matches!(
        Odometer::with_digits(vec![nat(3)], vec![nat(0), nat(0)]),
        Err(WindingError::LevelCountMismatch { .. })
    ));
}

#[test]
fn a_closed_loop_has_an_integer_winding_and_an_open_one_is_refused() {
    let modulus = BigInt::from(12);
    let closed = [BigInt::from(5), BigInt::from(-17), BigInt::from(24)];
    assert_eq!(
        closed_loop_winding(&modulus, &closed),
        Ok(BigInt::from(1)),
        "5 - 17 + 24 = 12 is one turn"
    );
    let open = [BigInt::from(5), BigInt::from(4)];
    assert_eq!(
        closed_loop_winding(&modulus, &open),
        Err(WindingError::LoopDoesNotClose {
            modulus: modulus.clone(),
            remainder: BigInt::from(9)
        }),
        "the exact remainder is retained, not rounded to a turn"
    );
    assert_eq!(
        closed_loop_winding(&BigInt::zero(), &closed),
        Err(WindingError::ZeroModulus)
    );
}

// -- 2. pair resonance ----------------------------------------------------------------------

#[test]
fn the_address_round_trips_with_its_ratio() {
    for p in 1i64..=18 {
        for q in 1i64..=18 {
            let address = LockAddress::from_ratio(&BigInt::from(p), &BigInt::from(q))
                .expect("a positive rate");
            let reduced = Rat::new(BigInt::from(p), BigInt::from(q));
            assert_eq!(
                address.to_ratio().expect("a unimodular word"),
                reduced,
                "address of {p}/{q} did not reopen"
            );
            assert_eq!(
                address.period().expect("a unimodular word"),
                *reduced.denom(),
                "the closure cost is the reduced denominator"
            );
            // The address is a function of the ratio, not of the spelling.
            let scaled = LockAddress::from_ratio(&BigInt::from(3 * p), &BigInt::from(3 * q))
                .expect("a positive rate");
            assert_eq!(address, scaled);
        }
    }
    assert!(
        LockAddress::from_ratio(&BigInt::from(1), &BigInt::from(1))
            .expect("the root")
            .runs()
            .is_empty()
    );
    assert_eq!(
        LockAddress::from_ratio(&BigInt::from(3), &BigInt::from(2))
            .expect("a positive rate")
            .runs(),
        &[
            LockRun {
                turn: Turn::R,
                length: nat(1)
            },
            LockRun {
                turn: Turn::L,
                length: nat(1)
            }
        ]
    );
    assert!(matches!(
        LockAddress::from_ratio(&BigInt::from(-1), &BigInt::from(2)),
        Err(WindingError::NotAPositiveRate { .. })
    ));
    assert!(matches!(
        LockAddress::from_ratio(&BigInt::from(1), &BigInt::zero()),
        Err(WindingError::NotAPositiveRate { .. })
    ));
}

#[test]
fn the_word_is_unimodular_and_integrally_invertible() {
    for p in 1i64..=12 {
        for q in 1i64..=12 {
            let matrix = LockAddress::from_ratio(&BigInt::from(p), &BigInt::from(q))
                .expect("a positive rate")
                .matrix()
                .expect("a unimodular word");
            assert!(matrix.determinant().is_one());
            let inverse = matrix.unimodular_inverse().expect("det one is invertible");
            assert_eq!(matrix.multiply(&inverse), IntMat2::identity());
            assert_eq!(inverse.multiply(&matrix), IntMat2::identity());
        }
    }
    let exchange = IntMat2::from_i64([[0, 1], [1, 0]]);
    assert_eq!(exchange.determinant(), BigInt::from(-1));
    assert_eq!(
        exchange
            .unimodular_inverse()
            .expect("det minus one is invertible")
            .multiply(&exchange),
        IntMat2::identity()
    );
    assert_eq!(
        IntMat2::from_i64([[2, 0], [0, 2]]).unimodular_inverse(),
        Err(WindingError::NonUnimodular {
            determinant: BigInt::from(4)
        })
    );
    assert_eq!(IntMat2::from_i64([[1, 2], [3, 4]]).trace(), BigInt::from(5));
}

#[test]
fn neighbours_have_a_mediant_that_neighbours_both() {
    let left = rat(1, 3);
    let right = rat(1, 2);
    assert!(are_neighbours(&left, &right));
    let middle = mediant(&left, &right);
    assert_eq!(middle, rat(2, 5));
    assert!(are_neighbours(&left, &middle));
    assert!(are_neighbours(&middle, &right));
    assert!(left < middle && middle < right, "the mediant lies between");
    assert!(!are_neighbours(&rat(1, 3), &rat(2, 3)));
}

#[test]
fn every_ratio_between_neighbours_costs_at_least_the_mediant() {
    // Exhaustive over the small Farey neighbours and every a/b strictly between them.
    for q in 1i64..=7 {
        for p in 0i64..=q {
            for q_prime in 1i64..=7 {
                for p_prime in 0i64..=q_prime {
                    let left = Rat::new(BigInt::from(p), BigInt::from(q));
                    let right = Rat::new(BigInt::from(p_prime), BigInt::from(q_prime));
                    if !are_neighbours(&left, &right) {
                        continue;
                    }
                    // The spelling may be unreduced; the cost is q + q' of the reduced pair.
                    let middle = mediant(&left, &right);
                    let cost = left.denom() + right.denom();
                    assert_eq!(*middle.denom(), cost);
                    for b in 1i64..=14 {
                        if BigInt::from(b) >= cost {
                            break;
                        }
                        for a in 0i64..=b {
                            let candidate = Rat::new(BigInt::from(a), BigInt::from(b));
                            assert!(
                                !(left < candidate && candidate < right),
                                "{a}/{b} is cheaper than the mediant of {p}/{q} and \
                                 {p_prime}/{q_prime}"
                            );
                        }
                    }
                    assert_eq!(
                        simplest_between(&left, &right).expect("a nonempty interval"),
                        middle,
                        "the mediant is the cheapest lock in the gap"
                    );
                }
            }
        }
    }
}

#[test]
fn simplest_between_agrees_with_brute_force() {
    let endpoints: Vec<Rat> = (-6i64..=6)
        .flat_map(|numerator| {
            (1i64..=5).map(move |denominator| {
                Rat::new(BigInt::from(numerator), BigInt::from(denominator))
            })
        })
        .collect();
    for lower in &endpoints {
        for upper in &endpoints {
            if lower >= upper {
                assert!(matches!(
                    simplest_between(lower, upper),
                    Err(WindingError::EmptyInterval { .. })
                ));
                continue;
            }
            let found = simplest_between(lower, upper).expect("a nonempty interval");
            assert!(*lower < found && found < *upper, "must lie strictly inside");
            // Brute force: no rational with a smaller denominator lies strictly inside.
            let bound = found.denom().clone();
            let mut minimal_witnesses: Vec<Rat> = Vec::new();
            let mut denominator = BigInt::one();
            while denominator <= bound {
                let span = 12i64;
                for numerator in -span * 6..=span * 6 {
                    let candidate = Rat::new(BigInt::from(numerator), denominator.clone());
                    if *candidate.denom() != denominator {
                        continue;
                    }
                    if *lower < candidate && candidate < *upper {
                        minimal_witnesses.push(candidate);
                    }
                }
                if !minimal_witnesses.is_empty() {
                    break;
                }
                denominator += BigInt::one();
            }
            assert_eq!(
                denominator, bound,
                "brute force found a cheaper denominator in ({lower}, {upper})"
            );
            if minimal_witnesses.len() == 1 {
                assert_eq!(minimal_witnesses[0], found);
            } else {
                assert!(minimal_witnesses.contains(&found));
            }
        }
    }
}

#[test]
fn a_locked_pair_reads_zero_slip_and_a_perturbed_one_does_not() {
    // Two pure translations along the axis: v_a = (0,0,2), v_b = (0,0,3), so 3 v_a = 2 v_b.
    let translating = |advance: i64| {
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::zero(), RatVec3::from_i64(0, 0, advance)),
            RatVec3::from_i64(1, -1, 0),
        )
    };
    let locked = ScrewPair::new(translating(2), translating(3));
    assert!(pair_lock(&locked, &BigInt::from(2), &BigInt::from(3)));
    assert!(!pair_lock(&locked, &BigInt::from(1), &BigInt::from(1)));
    let perturbed = ScrewPair::new(translating(2), translating(4));
    assert!(
        !pair_lock(&perturbed, &BigInt::from(2), &BigInt::from(3)),
        "a perturbed rate must not report a lock"
    );
    assert!(pair_lock(&perturbed, &BigInt::from(1), &BigInt::from(2)));

    // Two coaxial rotations at commensurate rates: v_a = (0,1,0), v_b = (0,2,0).
    let rotating = |rate: i64| {
        SituatedScrew::new(
            ScrewGenerator::new(RatVec3::from_i64(0, 0, rate), RatVec3::zero()),
            RatVec3::from_i64(1, 0, 0),
        )
    };
    let coaxial = ScrewPair::new(rotating(1), rotating(2));
    assert!(pair_lock(&coaxial, &BigInt::from(1), &BigInt::from(2)));
    assert!(!pair_lock(&coaxial, &BigInt::from(1), &BigInt::from(3)));
    assert_eq!(
        LockAddress::from_ratio(&BigInt::from(1), &BigInt::from(2))
            .expect("a positive rate")
            .period()
            .expect("a unimodular word"),
        BigInt::from(2)
    );
}

// -- 3. generator trace faces ---------------------------------------------------------------

type Mat2 = [[Rat; 2]; 2];

fn mat2_identity() -> Mat2 {
    [[Rat::one(), Rat::zero()], [Rat::zero(), Rat::one()]]
}

fn mat2_multiply(left: &Mat2, right: &Mat2) -> Mat2 {
    let entry = |row: usize, column: usize| {
        &left[row][0] * &right[0][column] + &left[row][1] * &right[1][column]
    };
    [[entry(0, 0), entry(0, 1)], [entry(1, 0), entry(1, 1)]]
}

fn mat2_trace(matrix: &Mat2) -> Rat {
    &matrix[0][0] + &matrix[1][1]
}

fn mat2_determinant(matrix: &Mat2) -> Rat {
    &matrix[0][0] * &matrix[1][1] - &matrix[0][1] * &matrix[1][0]
}

fn mat2_inverse(matrix: &Mat2) -> Mat2 {
    let determinant = mat2_determinant(matrix);
    assert!(
        !determinant.is_zero(),
        "the test carrier must be invertible"
    );
    [
        [
            &matrix[1][1] / &determinant,
            -(&matrix[0][1] / &determinant),
        ],
        [
            -(&matrix[1][0] / &determinant),
            &matrix[0][0] / &determinant,
        ],
    ]
}

#[test]
fn the_companion_powers_carry_the_trace_sequence() {
    for site in [
        SiteFactor::new(integer(3), integer(2)),
        SiteFactor::new(integer(-1), integer(5)),
        SiteFactor::new(rat(1, 2), rat(3, 4)),
    ] {
        let companion = site.companion();
        let sequence = site.trace_sequence(9);
        let mut power = mat2_identity();
        for (index, expected) in sequence.iter().enumerate() {
            assert_eq!(
                mat2_trace(&power),
                *expected,
                "tr(M^{index}) must be the trace sequence"
            );
            power = mat2_multiply(&power, &companion);
        }
        assert_eq!(mat2_trace(&companion), *site.trace());
        assert_eq!(mat2_determinant(&companion), *site.determinant());
    }
}

#[test]
fn conjugating_the_companion_moves_no_face() {
    let site = SiteFactor::new(rat(5, 2), integer(3));
    let carrier: Mat2 = [[rat(1, 2), integer(2)], [integer(3), integer(7)]];
    let conjugated = mat2_multiply(
        &mat2_multiply(&mat2_inverse(&carrier), &site.companion()),
        &carrier,
    );
    let carried = SiteFactor::new(mat2_trace(&conjugated), mat2_determinant(&conjugated));
    assert_eq!(carried.trace(), site.trace());
    assert_eq!(carried.determinant(), site.determinant());
    assert_eq!(
        carried.transfer_coefficients(),
        site.transfer_coefficients(),
        "the three transfer coefficients are conserved"
    );
    assert_eq!(carried.trace_sequence(8), site.trace_sequence(8));
    // And the conjugate's own power traces agree term by term.
    let mut power = mat2_identity();
    for expected in site.trace_sequence(8) {
        assert_eq!(mat2_trace(&power), expected);
        power = mat2_multiply(&power, &conjugated);
    }
}

#[test]
fn newtons_identities_link_the_machines_coefficients_and_traces() {
    let machine = Machine::new(vec![
        SiteFactor::new(integer(3), integer(2)),
        SiteFactor::new(integer(-1), integer(5)),
        SiteFactor::new(rat(1, 2), rat(3, 4)),
    ]);
    let coefficients = machine.transfer_determinant();
    assert_eq!(coefficients.len(), 7, "three sites give degree six");
    assert_eq!(coefficients[0], Rat::one());
    let degree = coefficients.len() - 1;
    let traces = machine.trace_sequence(degree);
    assert_eq!(traces[0], integer(6), "t_0 counts the machine's roots");
    for k in 1..=degree {
        let mut right = Rat::zero();
        for index in 1..=k {
            right -= &coefficients[k - index] * &traces[index];
        }
        assert_eq!(
            &coefficients[k] * &integer(k as i64),
            right,
            "Newton's identity failed at k = {k}"
        );
    }
    // The product of the two single-site factors is the two-site machine's factor.
    let pair = Machine::new(vec![
        SiteFactor::new(integer(3), integer(2)),
        SiteFactor::new(integer(-1), integer(5)),
    ]);
    assert_eq!(
        pair.transfer_determinant(),
        vec![
            integer(1),
            integer(-2),
            integer(4),
            integer(-13),
            integer(10)
        ],
        "(1-3T+2T^2)(1+T+5T^2)"
    );
}

#[test]
fn the_discriminant_classifies_the_site_and_a_shared_q_is_reported() {
    assert_eq!(
        SiteFactor::new(integer(1), integer(1)).kind(),
        SiteKind::Rotation
    );
    assert_eq!(
        SiteFactor::new(integer(4), integer(4)).kind(),
        SiteKind::Marginal
    );
    assert_eq!(
        SiteFactor::new(integer(5), integer(4)).kind(),
        SiteKind::Dilation
    );
    assert_eq!(
        SiteFactor::new(rat(1, 2), rat(1, 16)).kind(),
        SiteKind::Marginal,
        "a^2 = 1/4 = 4q exactly"
    );
    assert_eq!(
        Machine::new(vec![
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(2)),
        ])
        .common_dilation(),
        Some(integer(2))
    );
    assert_eq!(
        Machine::new(vec![
            SiteFactor::new(integer(3), integer(2)),
            SiteFactor::new(integer(-1), integer(5)),
        ])
        .common_dilation(),
        None
    );
    assert_eq!(Machine::default().common_dilation(), None);
    assert_eq!(Machine::default().transfer_determinant(), vec![Rat::one()]);
}

// -- 4. cell holonomy -----------------------------------------------------------------------

fn gauge(parameter: Rat, translation: RatVec3) -> AffineMap3 {
    AffineMap3 {
        linear: cayley_rotation_z(&parameter),
        translation,
    }
}

#[test]
fn regauging_conjugates_the_holonomy() {
    let k0 = gauge(rat(1, 2), RatVec3::from_i64(1, -2, 3));
    let k1 = gauge(rat(-1, 3), RatVec3::from_i64(0, 4, -1));
    let k2 = gauge(integer(2), RatVec3::from_i64(-3, 1, 5));
    let g01 = gauge(rat(1, 4), RatVec3::from_i64(2, 0, -1));
    let g12 = gauge(rat(3, 5), RatVec3::from_i64(-1, 1, 1));
    let g20 = gauge(integer(1), RatVec3::from_i64(0, -2, 4));

    let holonomy = triangle_holonomy(&g01, &g12, &g20);
    let regauged = triangle_holonomy(
        &regauge(&k0, &k1, &g01).expect("an invertible frame"),
        &regauge(&k1, &k2, &g12).expect("an invertible frame"),
        &regauge(&k2, &k0, &g20).expect("an invertible frame"),
    );
    let conjugated = k0
        .inverse()
        .expect("an invertible frame")
        .followed_by(&holonomy)
        .followed_by(&k0);
    assert_eq!(
        regauged, conjugated,
        "regauging conjugates by the base frame"
    );
    assert_eq!(
        linear_trace(&regauged),
        linear_trace(&holonomy),
        "the trace of the linear part is gauge free"
    );
    assert_eq!(regauged.linear.determinant(), holonomy.linear.determinant());
    let singular = AffineMap3 {
        linear: RatMat3::from_i64([[1, 0, 0], [0, 1, 0], [0, 0, 0]]),
        translation: RatVec3::zero(),
    };
    assert_eq!(
        regauge(&singular, &k1, &g01),
        Err(WindingError::SingularGauge)
    );
}

#[test]
fn a_pure_gauge_has_identity_holonomy() {
    let k0 = gauge(rat(2, 3), RatVec3::from_i64(5, 1, -2));
    let k1 = gauge(rat(-1, 2), RatVec3::from_i64(1, 1, 1));
    let k2 = gauge(integer(3), RatVec3::from_i64(-4, 0, 2));
    let identity = AffineMap3::identity();
    let holonomy = triangle_holonomy(
        &regauge(&k0, &k1, &identity).expect("an invertible frame"),
        &regauge(&k1, &k2, &identity).expect("an invertible frame"),
        &regauge(&k2, &k0, &identity).expect("an invertible frame"),
    );
    assert_eq!(holonomy, identity, "a pure gauge carries no face");
    assert_eq!(linear_trace(&holonomy), integer(3));
    assert_eq!(
        burgers_step(&holonomy).expect("a flat holonomy"),
        &RatVec3::zero()
    );
}

#[test]
fn three_translations_give_the_burgers_step() {
    let translation = |x: i64, y: i64, z: i64| AffineMap3 {
        linear: RatMat3::identity(),
        translation: RatVec3::from_i64(x, y, z),
    };
    let first = translation(1, 2, 3);
    let second = translation(-4, 0, 5);
    let third = translation(2, 1, -1);
    let holonomy = triangle_holonomy(&first, &second, &third);
    assert_eq!(
        burgers_step(&holonomy).expect("a flat holonomy"),
        &RatVec3::from_i64(-1, 3, 7),
        "the Burgers step is the sum of the lifted increments"
    );
    // And it is zero exactly when the lifted loop closes.
    let closing = translation(3, -2, -8);
    let closed = triangle_holonomy(&first, &second, &closing);
    assert_eq!(
        burgers_step(&closed).expect("a flat holonomy"),
        &RatVec3::zero()
    );
    assert_eq!(closed, AffineMap3::identity());
    // The same closure read on one axis through the lifted integer winding.
    assert_eq!(
        closed_loop_winding(
            &BigInt::from(1),
            &[BigInt::from(3), BigInt::from(5), BigInt::from(-8)]
        ),
        Ok(BigInt::zero())
    );
    let curved = triangle_holonomy(&first, &gauge(integer(1), RatVec3::zero()), &third);
    assert_eq!(burgers_step(&curved), Err(WindingError::CurvedHolonomy));
}
