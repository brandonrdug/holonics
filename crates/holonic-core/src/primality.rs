//! **Primality, decided: deterministic Miller–Rabin over twelve fixed bases, exact for every `u64`.**
//!
//! [definition] Moved from `holonic_engine::topological_receiver` with the certified prime-image
//! reading, whose charts must be decided prime ([`crate::prime_image_algebra::PrimeChart`]). The
//! topological receiver imports it from here. The base set is a proof: no composite below
//! `3.317 × 10^24` is a strong pseudoprime to all twelve (Sorenson–Webster), and `2^64` sits far
//! inside that range, so nothing here is probabilistic.

/// The twelve bases whose strong-pseudoprime test is a primality *proof* below `3.317 × 10^24`.
const MILLER_RABIN_BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// `left · right mod modulus`, through a 128-bit product so nothing wraps.
fn multiply_modulo(left: u64, right: u64, modulus: u64) -> u64 {
    ((u128::from(left) * u128::from(right)) % u128::from(modulus)) as u64
}

/// `base^exponent mod modulus`, by exact square-and-multiply.
fn power_modulo(base: u64, mut exponent: u64, modulus: u64) -> u64 {
    let mut standing = base % modulus;
    let mut accumulated = 1_u64 % modulus;
    while exponent > 0 {
        if exponent & 1 == 1 {
            accumulated = multiply_modulo(accumulated, standing, modulus);
        }
        standing = multiply_modulo(standing, standing, modulus);
        exponent >>= 1;
    }
    accumulated
}

/// **Primality, decided.** Deterministic Miller–Rabin over [`MILLER_RABIN_BASES`], which is exact
/// for every `u64`. No probabilistic acceptance and no early exit on a guess.
pub fn is_prime(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    for base in MILLER_RABIN_BASES {
        if value == base {
            return true;
        }
        if value.is_multiple_of(base) {
            return false;
        }
    }
    // `value` is odd and larger than every base, so `value − 1 = odd · 2^twos` with `twos ≥ 1`.
    let mut odd = value - 1;
    let mut twos = 0_u32;
    while odd.is_multiple_of(2) {
        odd /= 2;
        twos += 1;
    }
    'base: for base in MILLER_RABIN_BASES {
        let mut standing = power_modulo(base, odd, value);
        if standing == 1 || standing == value - 1 {
            continue;
        }
        for _ in 1..twos {
            standing = multiply_modulo(standing, standing, value);
            if standing == value - 1 {
                continue 'base;
            }
        }
        return false;
    }
    true
}
