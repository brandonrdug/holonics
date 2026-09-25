//! **Primes of the machine: the primitive cycles of a return map and its Euler product.**
//!
//! [definition] A finite **return map** of occurrences is a map `f` of a finite set, with the `0/1`
//! matrix `M_f` (`M_f x y = [f x = y]`, Lean `Aeon/Production/Zeta.mapMatrix`), or more generally a
//! `0/1` matrix, the adjacency of a directed graph without multiple edges. Its closed-aeon counts
//! are `N_n = tr(Mⁿ)` ([`crate::aeon::ReturnMap::cycle_counts`]). A **primitive cycle** of
//! length `d` is a closed walk of least period `d` up to rotation: for a map, a periodic orbit of
//! least period `d`. Its count `p_d` is a prime count of the machine:
//!
//! ```text
//! N_n = Σ_(d|n) d·p_d          d·p_d = Σ_(m|d) μ(d/m) N_m          (Möbius inversion)
//! det(1 − T·M) = ∏_d (1 − T^d)^(p_d)                              (the Euler product)
//! exp(Σ_n N_n Tⁿ/n) · ∏_d (1 − T^d)^(p_d) = 1                    (ζ is the product over primes)
//! ```
//!
//! [proved-derived; implemented-exact] For the matrix of a map the product is finite and equals the
//! transfer determinant as a polynomial; the primitive cycles are enumerated as orbits and the
//! counts recovered by inversion agree with them. For a general `0/1` matrix the inverted `p_d` are
//! the necklace counts of primitive closed walks and the product is infinite; it is returned
//! truncated at the declared horizon, where it agrees with `det(1 − T·M)`. Their integrality and the
//! infinite product are owed in #62 (Lean `PrimitiveCycle`, "the necklace integrality and the
//! infinite product"); an integral, nonnegative count is checked at every `d` and anything else
//! refused.
//!
//! [definition] **Only `0/1` return maps.** A signed or general integer matrix (the navigator
//! machine's companions `1 − aT + qT²`, `[[−1]]`, `[[2]]`) is refused by name: `[[−1]]` has
//! `N_1 = −1`, which no set of occurrences realizes (Lean `signed_map_has_no_primitive_cycles`),
//! and a multigraph's necklace case is not this law.
//!
//! | Lean `Compression/Landmark/PrimitiveCycle` | Rust |
//! |---|---|
//! | `primitiveCycles`, `primitiveCount` | [`ReturnOccurrences::primitive_cycles`], [`ReturnOccurrences::primitive_counts`] |
//! | `card_minimalPeriod_eq`, `primitiveCount_eq_zero_of_card_lt`, `periodic_count`, `trace_pow_eq_primitive` | tests |
//! | `primitive_count_moebius` | [`ReturnOccurrences::primitive_counts`] |
//! | `transfer_determinant_euler_product`, `zeta_euler_product` | [`ReturnOccurrences::euler_product`] |
//! | `signed_map_has_no_primitive_cycles` | [`ReturnOccurrences::of_zero_one`] |

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::aeon::ReturnMap;
use crate::compression::landmark::LandmarkError;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

/// The Möbius function `μ(n)` of a positive natural: `0` with a square factor, else `(−1)^(#primes)`.
/// `μ` is defined only on positive naturals, and the one caller passes a quotient
/// `length / divisor` of a divisor, which is at least one.
fn moebius(value: usize) -> i64 {
    let mut remaining = value;
    let mut sign = 1;
    let mut factor = 2;
    while factor * factor <= remaining {
        if remaining % factor == 0 {
            remaining /= factor;
            if remaining % factor == 0 {
                return 0;
            }
            sign = -sign;
        }
        factor += 1;
    }
    if remaining > 1 {
        sign = -sign;
    }
    sign
}

/// [definition] **A `0/1` return map of occurrences**, and the map it comes from when it has one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnOccurrences {
    matrix: ExactRatMatrix,
    map: Option<Vec<usize>>,
}

impl ReturnOccurrences {
    /// The return map of `f`, `f(x) = images[x]`; an image outside the occurrences is refused.
    pub fn of_map(images: Vec<usize>) -> Result<Self, LandmarkError> {
        let size = images.len();
        let mut rows = vec![vec![Rat::zero(); size]; size];
        for (occurrence, image) in images.iter().enumerate() {
            if *image >= size {
                return Err(LandmarkError::MapImage {
                    occurrence,
                    image: *image,
                    size,
                });
            }
            rows[occurrence][*image] = Rat::one();
        }
        Ok(Self {
            matrix: ExactRatMatrix::shaped(size, size, rows)?,
            map: Some(images),
        })
    }

    /// A `0/1` return map; any other entry, and a nonsquare matrix, is refused by name.
    pub fn of_zero_one(matrix: ExactRatMatrix) -> Result<Self, LandmarkError> {
        if !matrix.is_square() {
            return Err(LandmarkError::NotSquare {
                rows: matrix.rows(),
                columns: matrix.columns(),
            });
        }
        for row in 0..matrix.rows() {
            for column in 0..matrix.columns() {
                let entry = matrix.get(row, column)?;
                if !entry.is_zero() && !entry.is_one() {
                    return Err(LandmarkError::NotZeroOne {
                        row,
                        column,
                        entry: entry.clone(),
                    });
                }
            }
        }
        Ok(Self { matrix, map: None })
    }

    /// The `0/1` matrix.
    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }

    fn return_map(&self) -> ReturnMap {
        ReturnMap::Matrix(self.matrix.clone())
    }

    /// **The closed-aeon counts** `N_n = tr(Mⁿ)`, `n = 0, …, horizon`.
    pub fn cycle_counts(&self, horizon: usize) -> Result<Vec<BigInt>, LandmarkError> {
        self.return_map()
            .cycle_counts(horizon)?
            .into_iter()
            .enumerate()
            .map(|(length, count)| {
                count
                    .is_integer()
                    .then(|| count.to_integer())
                    .ok_or(LandmarkError::NonIntegralCount { length })
            })
            .collect()
    }

    /// **The primitive counts by Möbius inversion**, `d·p_d = Σ_(m|d) μ(d/m) N_m`, for
    /// `d = 0, …, horizon` with `p_0 = 0` (Lean `primitive_count_moebius`); a count that is not a
    /// nonnegative integer is refused.
    pub fn primitive_counts(&self, horizon: usize) -> Result<Vec<BigInt>, LandmarkError> {
        let counts = self.cycle_counts(horizon)?;
        let mut primitive = vec![BigInt::zero(); horizon + 1];
        for length in 1..=horizon {
            let mut total = BigInt::zero();
            for divisor in (1..=length).filter(|divisor| length % divisor == 0) {
                total += BigInt::from(moebius(length / divisor)) * &counts[divisor];
            }
            let length_integer = BigInt::from(length);
            if !(&total % &length_integer).is_zero() || total.is_negative() {
                return Err(LandmarkError::NonIntegralCount { length });
            }
            primitive[length] = total / length_integer;
        }
        Ok(primitive)
    }

    /// **The primitive cycles of a map**, each as its occurrences from the least one, ordered by
    /// that occurrence; `None` for a `0/1` matrix that is not a map's.
    pub fn primitive_cycles(&self) -> Option<Vec<Vec<usize>>> {
        let images = self.map.as_ref()?;
        let size = images.len();
        let mut state = vec![0u8; size];
        let mut cycles = Vec::new();
        for start in 0..size {
            let mut path = Vec::new();
            let mut occurrence = start;
            while state[occurrence] == 0 {
                state[occurrence] = 1;
                path.push(occurrence);
                occurrence = images[occurrence];
            }
            if state[occurrence] == 1 {
                let entry = path
                    .iter()
                    .position(|visited| *visited == occurrence)
                    .unwrap_or(0);
                let mut cycle = path[entry..].to_vec();
                let least = cycle
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, value)| **value)
                    .map_or(0, |(index, _)| index);
                cycle.rotate_left(least);
                cycles.push(cycle);
            }
            for visited in path {
                state[visited] = 2;
            }
        }
        cycles.sort();
        Some(cycles)
    }

    /// **The Euler product** `∏_(d≤horizon) (1 − T^d)^(p_d)` through `T^horizon`, each factor
    /// expanded by the binomial theorem (Lean `transfer_determinant_euler_product`).
    pub fn euler_product(&self, horizon: usize) -> Result<Vec<BigInt>, LandmarkError> {
        let primitive = self.primitive_counts(horizon)?;
        let mut product = vec![BigInt::zero(); horizon + 1];
        product[0] = BigInt::one();
        for (length, count) in primitive.iter().enumerate().skip(1) {
            if count.is_zero() {
                continue;
            }
            let mut factor = vec![BigInt::zero(); horizon + 1];
            let mut binomial = BigInt::one();
            let mut power = 0usize;
            while power * length <= horizon && BigInt::from(power) <= *count {
                let sign = if power % 2 == 0 {
                    BigInt::one()
                } else {
                    -BigInt::one()
                };
                factor[power * length] = &sign * &binomial;
                binomial = binomial * (count - BigInt::from(power)) / BigInt::from(power + 1);
                power += 1;
            }
            let mut next = vec![BigInt::zero(); horizon + 1];
            for (left, left_coefficient) in product.iter().enumerate() {
                if left_coefficient.is_zero() {
                    continue;
                }
                for (right, right_coefficient) in factor.iter().enumerate().take(horizon + 1 - left)
                {
                    next[left + right] += left_coefficient * right_coefficient;
                }
            }
            product = next;
        }
        Ok(product)
    }

    /// The transfer determinant `det(1 − T·M)`, lowest power first.
    pub fn transfer_determinant(&self) -> Result<Vec<Rat>, LandmarkError> {
        Ok(self.return_map().transfer_determinant()?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::cycle_exponential;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::integer_matrix;

    /// Maps with fixed points, a transposition, a three-cycle, tails and one long cycle.
    fn maps() -> Vec<Vec<usize>> {
        vec![
            vec![1, 2, 0, 4, 3, 5, 5],
            vec![0, 1, 2],
            vec![1, 2, 3, 4, 5, 0],
            vec![1, 0, 3, 4, 2, 1, 7, 8, 6, 6],
            vec![0],
        ]
    }

    fn big(values: &[i64]) -> Vec<BigInt> {
        values.iter().map(|value| BigInt::from(*value)).collect()
    }

    /// The least period of an occurrence on a cycle of the map.
    fn least_period(images: &[usize], occurrence: usize) -> Option<usize> {
        let mut current = images[occurrence];
        for period in 1..=images.len() {
            if current == occurrence {
                return Some(period);
            }
            current = images[current];
        }
        None
    }

    /// Lean `card_minimalPeriod_eq`, `primitiveCount_eq_zero_of_card_lt`: the occurrences of least
    /// period `d` number `d·p_d`, and no primitive cycle is longer than the occurrence set.
    #[test]
    fn a_primitive_cycle_carries_its_length_in_occurrences() {
        for images in maps() {
            let size = images.len();
            let map = ReturnOccurrences::of_map(images.clone()).unwrap();
            let cycles = map.primitive_cycles().unwrap();
            let horizon = size + 3;
            let primitive = map.primitive_counts(horizon).unwrap();
            for length in 1..=horizon {
                let periodic = (0..size)
                    .filter(|x| least_period(&images, *x) == Some(length))
                    .count();
                let enumerated = cycles.iter().filter(|cycle| cycle.len() == length).count();
                assert_eq!(BigInt::from(enumerated), primitive[length]);
                assert_eq!(
                    BigInt::from(periodic),
                    BigInt::from(length) * &primitive[length]
                );
                if length > size {
                    assert!(primitive[length].is_zero());
                }
            }
        }
    }

    /// Lean `periodic_count`, `trace_pow_eq_primitive`, `primitive_count_moebius`:
    /// `tr(M_fⁿ) = Σ_(d|n) d·p_d` over the enumerated orbits, and Möbius inversion of the counts
    /// returns exactly those orbits' counts.
    #[test]
    fn the_counts_are_the_primitive_cycles_over_the_divisors() {
        for images in maps() {
            let map = ReturnOccurrences::of_map(images).unwrap();
            let cycles = map.primitive_cycles().unwrap();
            let counts = map.cycle_counts(12).unwrap();
            for (n, count) in counts.iter().enumerate().skip(1) {
                let from_cycles: usize = cycles
                    .iter()
                    .map(Vec::len)
                    .filter(|length| n % length == 0)
                    .sum();
                assert_eq!(*count, BigInt::from(from_cycles));
            }
        }
        assert_eq!(moebius(1), 1);
        assert_eq!(moebius(6), 1);
        assert_eq!(moebius(12), 0);
        assert_eq!(moebius(30), -1);
    }

    /// Lean `transfer_determinant_euler_product`, `zeta_euler_product`: the finite Euler product of a
    /// map's primitive cycles is its transfer determinant as a polynomial, and it multiplies the
    /// exponential of the cycle series to `1`.
    #[test]
    fn the_euler_product_of_a_map_is_its_transfer_determinant() {
        for images in maps() {
            let size = images.len();
            let map = ReturnOccurrences::of_map(images).unwrap();
            let horizon = size + 4;
            let product = map.euler_product(horizon).unwrap();
            let mut transfer = map.transfer_determinant().unwrap();
            transfer.resize(horizon + 1, Rat::zero());
            let product_rat: Vec<Rat> = product.iter().cloned().map(Rat::from_integer).collect();
            assert_eq!(product_rat, transfer);
            let zeta =
                cycle_exponential(&ReturnMap::Matrix(map.matrix().clone()), horizon).unwrap();
            for degree in 0..=horizon {
                let coefficient: Rat = (0..=degree)
                    .map(|split| &zeta[split] * &product_rat[degree - split])
                    .sum();
                assert_eq!(coefficient, integer(i64::from(degree == 0)));
            }
        }
    }

    /// The golden-mean shift `[[1, 1], [1, 0]]` is a `0/1` matrix but not a map: its counts are the
    /// Lucas numbers, its inverted primitive counts the necklaces `1, 1, 1, 1, 2, 2, 4, 5, 8, 11`,
    /// and the truncated infinite Euler product is `1 − T − T²` through every horizon (the necklace
    /// case, owed in #62).
    #[test]
    fn a_zero_one_matrix_has_necklace_primes_and_an_infinite_product() {
        let shift =
            ReturnOccurrences::of_zero_one(integer_matrix(&[&[1, 1], &[1, 0]]).unwrap()).unwrap();
        assert_eq!(shift.primitive_cycles(), None);
        assert_eq!(
            shift.cycle_counts(10).unwrap(),
            big(&[2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123])
        );
        assert_eq!(
            shift.primitive_counts(10).unwrap(),
            big(&[0, 1, 1, 1, 1, 2, 2, 4, 5, 8, 11])
        );
        for horizon in [2usize, 5, 12, 20] {
            let mut expected = big(&[1, -1, -1]);
            expected.resize(horizon + 1, BigInt::zero());
            assert_eq!(shift.euler_product(horizon).unwrap(), expected);
        }
    }

    /// Lean `signed_map_has_no_primitive_cycles`: `[[−1]]` is refused, as are a multigraph's `[[2]]`
    /// and a navigator site's companion `[[3, −2], [1, 0]]`; a map's image outside its occurrences
    /// is refused.
    #[test]
    fn signed_and_integer_return_maps_are_refused() {
        for rows in [vec![vec![-1]], vec![vec![2]], vec![vec![3, -2], vec![1, 0]]] {
            let slices: Vec<&[i64]> = rows.iter().map(Vec::as_slice).collect();
            assert!(matches!(
                ReturnOccurrences::of_zero_one(integer_matrix(&slices).unwrap()),
                Err(LandmarkError::NotZeroOne { .. })
            ));
        }
        assert_eq!(
            ReturnOccurrences::of_map(vec![0, 3]),
            Err(LandmarkError::MapImage {
                occurrence: 1,
                image: 3,
                size: 2
            })
        );
    }
}
