//! The Holonics patch of `gcd` returns the value Euclid's algorithm returns.
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::Zero;

fn euclid(a: &BigUint, b: &BigUint) -> BigUint {
    let (mut a, mut b) = (a.clone(), b.clone());
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

#[test]
fn patched_gcd_is_euclid() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut word = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        state
    };
    let mut values = Vec::new();
    for limbs in 0..6 {
        for _ in 0..40 {
            let digits: Vec<u32> = (0..2 * limbs).map(|_| word() as u32).collect();
            let v = BigUint::new(digits);
            values.push(&v << (word() % 70));
        }
    }
    for k in 0..200u32 {
        values.push(BigUint::from(1u8) << k);
        values.push((BigUint::from(1u8) << k) * 3u8);
    }
    let shared = values[50].clone();
    for (i, a) in values.iter().enumerate() {
        for b in values.iter().skip(i % 7).step_by(7) {
            assert_eq!(a.gcd(b), euclid(a, b));
            let (x, y) = (a * &shared, b * &shared);
            assert_eq!(x.gcd(&y), euclid(&x, &y));
        }
    }
}
