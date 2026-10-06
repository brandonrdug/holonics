//! **Primality, decided: deterministic Miller–Rabin over the first twelve prime bases, exact for
//! every `u64`.**
//!
//! [proved-standard] The base set is a proof, not a heuristic. `ψ₁₂`, the least composite that is a
//! strong pseudoprime to every one of the twelve prime bases `2, 3, …, 37`, is
//! `318665857834031151167461` (Sorenson–Webster). Every composite below it is caught by one of the
//! bases, and `2^64 − 1 < ψ₁₂`, so nothing here is probabilistic. The certified prime-image reading
//! decides its charts prime with this.

/// The first twelve prime bases.
const MILLER_RABIN_BASES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

/// `ψ₁₂`: the least composite that is a strong pseudoprime to all of [`MILLER_RABIN_BASES`].
const PSI_12: u128 = 318_665_857_834_031_151_167_461;

// The proof covers the whole `u64` domain.
const _: () = assert!((u64::MAX as u128) < PSI_12);

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

/// **Primality, decided.** Deterministic Miller–Rabin over [`MILLER_RABIN_BASES`], exact for every
/// `u64` because every `u64` lies below [`PSI_12`].
pub(crate) fn is_prime(value: u64) -> bool {
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

#[cfg(test)]
mod tests {
    use super::*;

    /// The twelve-base proof holds below `ψ₁₂ = 318665857834031151167461`, which lies above
    /// `2^64 − 1`; on the covered range the test agrees with trial division, and it rejects the
    /// strong pseudoprime `3215031751` to the bases `2, 3, 5, 7`.
    #[test]
    fn the_twelve_base_test_is_exact_below_psi_twelve() {
        assert_eq!(PSI_12, 318_665_857_834_031_151_167_461);
        assert!(u128::from(u64::MAX) < PSI_12);
        let trial = |n: u64| n >= 2 && (2..).take_while(|d| d * d <= n).all(|d| n % d != 0);
        for n in 0..20_000_u64 {
            assert_eq!(is_prime(n), trial(n), "{n}");
        }
        assert!(!is_prime(3_215_031_751));
        assert!(is_prime(18_446_744_073_709_551_557));
    }
}
