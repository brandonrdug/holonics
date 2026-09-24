use super::*;

fn surface() -> Option<(&'static ResidentReadout, &'static ResidentSurface<'static>)> {
    let readout = match ResidentReadout::new() {
        Ok(readout) => Box::leak(Box::new(readout)),
        Err(_) => {
            eprintln!("no resident chart answered; the resident-section tests did not run");
            return None;
        }
    };
    let surface = Box::leak(Box::new(ResidentSurface::on(readout).ok()?));
    Some((readout, surface))
}

/// The kernel's helpers against an independent exact reference: signed minimum, its negation,
/// negative shifts both ways, shifts by the carrier width, zero, positive and negative interval
/// products, denominators touching zero, and the negative quotient enclosure.
#[test]
#[ignore = "requires CUDA; host/device parity of the exact resident-section kernel arithmetic"]
fn the_arithmetic_helpers_agree_with_the_serial_exact_reference_on_the_signed_edge_cases() {
    let (_, surface) = surface().expect("a CUDA device mounts the resident surface");
    let cases: Vec<(i64, i64, i32, i64)> = vec![
        (i64::MIN, 3, 0, 0),
        (i64::MIN, 3, -1, 0),
        (i64::MIN, 3, 40, 0),
        (i64::MIN + 1, 7, -3, 0),
        (-7, 2, -1, 0),
        (-7, 2, 1, 0),
        (7, 2, -1, 0),
        (-1, 1, -70, 0),
        (1, 1, -70, 0),
        (0, 5, 60, 0),
        (-2, 1, 1, 1), // interval quotient N=[-2,-1], D=[1,2] lifted by 1
        (-2, 1, 0, 1), // corners of [-2,-1]·[1,2]
        (3, 4, 0, 2),  // corners of [3,5]·[4,6]
        (-5, 3, 0, 4), // corners of [-5,-1]·[3,7]
        (i64::MAX, i64::MAX, 0, 0),
        (-i64::MAX, i64::MAX, 3, 0),
        (5, 0, 0, 0),   // denominator zero: refused, not divided
        (5, 1, 126, 0), // shift by the carrier width refuses
        (1, 1, 127, 0),
    ];
    let a: Vec<i64> = cases.iter().map(|c| c.0).collect();
    let b: Vec<i64> = cases.iter().map(|c| c.1).collect();
    let s: Vec<i32> = cases.iter().map(|c| c.2).collect();
    let span: Vec<i64> = cases.iter().map(|c| c.3).collect();
    let (results, flags) = surface
        .arithmetic_control(&a, &b, &s, &span)
        .expect("control");
    let two = BigInt::from(2);
    let pow = |k: u32| BigInt::from(BigUint::from(1u8) << k as usize);
    let floor_div = |n: &BigInt, d: &BigInt| -> BigInt {
        let q = n / d;
        if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) != (d < &BigInt::from(0))) {
            q - 1
        } else {
            q
        }
    };
    let ceil_div = |n: &BigInt, d: &BigInt| -> BigInt {
        let q = n / d;
        if (n % d) != BigInt::from(0) && ((n < &BigInt::from(0)) == (d < &BigInt::from(0))) {
            q + 1
        } else {
            q
        }
    };
    let carrier = pow(127);
    for (i, (av, bv, sv, sp)) in cases.iter().enumerate() {
        let a = BigInt::from(*av);
        let b = BigInt::from(*bv);
        let row = results[i];
        let flag = flags[i];
        // shift_floor / shift_ceil against the exact rational
        let (expected_floor, expected_ceil, overflow) = if *sv >= 0 {
            let value = &a * pow(*sv as u32);
            let overflow = value.magnitude() >= carrier.magnitude();
            (value.clone(), value, overflow)
        } else {
            let d = pow((-*sv) as u32);
            (floor_div(&a, &d), ceil_div(&a, &d), false)
        };
        if overflow {
            assert!(
                flag & REFUSED_CARRIER != 0,
                "case {i}: an overflowing shift must refuse"
            );
        } else {
            assert_eq!(BigInt::from(row[0]), expected_floor, "case {i} floor");
            assert_eq!(BigInt::from(row[1]), expected_ceil, "case {i} ceil");
        }
        // product_shift(a, b, |s|): floor and ceil of a·b / 2^|s|
        let k = sv.unsigned_abs();
        let product = &a * &b;
        let d = pow(k);
        if product.magnitude() < pow(253).magnitude() {
            let pf = floor_div(&product, &d);
            let pc = ceil_div(&product, &d);
            if pf.magnitude() <= pow(126).magnitude() && pc.magnitude() <= pow(126).magnitude() {
                assert_eq!(BigInt::from(row[2]), pf, "case {i} product floor");
                assert_eq!(BigInt::from(row[3]), pc, "case {i} product ceil");
            }
        }
        // div_floor / div_ceil for b > 0
        if *bv > 0 {
            assert_eq!(
                BigInt::from(row[4]),
                floor_div(&a, &b),
                "case {i} div floor"
            );
            assert_eq!(BigInt::from(row[5]), ceil_div(&a, &b), "case {i} div ceil");
            // the interval quotient of [a, a+span] / [b, b+span], lifted by one
            let n_lo = &a * &two;
            let n_hi = (&a + BigInt::from(*sp)) * &two;
            let d_lo = b.clone();
            let d_hi = &b + BigInt::from(*sp);
            let q_lo = floor_div(&n_lo, if n_lo < BigInt::from(0) { &d_lo } else { &d_hi });
            let q_hi = ceil_div(&n_hi, if n_hi < BigInt::from(0) { &d_hi } else { &d_lo });
            if n_lo.magnitude() < carrier.magnitude() && n_hi.magnitude() < carrier.magnitude() {
                assert_eq!(BigInt::from(row[6]), q_lo, "case {i} quotient lo");
                assert_eq!(BigInt::from(row[7]), q_hi, "case {i} quotient hi");
            }
        } else {
            assert!(
                flag & REFUSED_MALFORMED != 0,
                "case {i}: a non-positive denominator must refuse"
            );
        }
        // corners of [a, a+span]·[b, b+span]
        let ends = [
            &a * &b,
            &a * (&b + BigInt::from(*sp)),
            (&a + BigInt::from(*sp)) * &b,
            (&a + BigInt::from(*sp)) * (&b + BigInt::from(*sp)),
        ];
        let c_lo = ends.iter().min().cloned().expect("four");
        let c_hi = ends.iter().max().cloned().expect("four");
        if c_lo.magnitude() < carrier.magnitude() && c_hi.magnitude() < carrier.magnitude() {
            assert_eq!(BigInt::from(row[8]), c_lo, "case {i} corners lo");
            assert_eq!(BigInt::from(row[9]), c_hi, "case {i} corners hi");
        }
    }
    // The named negative quotient: N=[-2,-1] over D=[1,2] is exactly [-2, -1/2].
    let named = cases
        .iter()
        .position(|c| *c == (-2, 1, 1, 1))
        .expect("the named case");
    assert_eq!(results[named][6], -4, "lo = -2 at half-grain resolution");
    assert_eq!(results[named][7], -1, "hi = -1/2 at half-grain resolution");
    assert_eq!(flags[named], 0);
}
