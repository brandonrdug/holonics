//! Exact checks of `Geometry/PhaseCarry` and `Transport/CellHolonomy`.

use super::*;
use crate::geometry::cayley_rotation_z;
use crate::ratio::{integer, rat};

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
