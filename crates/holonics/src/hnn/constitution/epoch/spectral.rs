//! Certified spectral readings for grouped dyadic epoch arrays.
//!
//! Refresh uses the established deposition law on a transient 16-significant-bit integer face.
//! The retained `EpochArray` is never changed or expanded to per-entry rationals; the face error
//! is carried as an explicit Frobenius bound. Between aeon refreshes, actual map moves accumulate
//! their grouped Frobenius upper bounds by the triangle inequality.

use super::EpochArray;
use crate::hnn::HnnError;
use crate::holon::deposition::{dyadic, root_ceiling, significant};
use crate::ratio::Rat;
use crate::ratio::linear::vector::integer_dot;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

/// A certified upper bound for one locus map, refreshed from its Gram at aeon close and carried
/// between closes by the Frobenius bounds of its actual moves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochSpectral {
    rows: usize,
    columns: usize,
    gram_bound: Rat,
    move_bound: Rat,
}

impl EpochSpectral {
    /// The founded zero map has zero spectral bound and no accumulated move.
    pub(crate) fn founded_zero(rows: usize, columns: usize) -> Self {
        Self {
            rows,
            columns,
            gram_bound: Rat::zero(),
            move_bound: Rat::zero(),
        }
    }

    /// Refresh from the actual grouped map at aeon close. The matrix is consumed as integer
    /// coordinates over its shared dyadic denominator; only the transient Gram face is formed.
    pub(crate) fn refresh(&mut self, map: &EpochArray) -> Result<(), HnnError> {
        self.admit_shape(map)?;
        self.gram_bound = grouped_spectral_bound(map)?;
        self.move_bound = Rat::zero();
        Ok(())
    }

    /// Carry the actual represented map move until the next aeon close.
    pub(crate) fn observe_move(&mut self, delta: &EpochArray) -> Result<(), HnnError> {
        self.admit_shape(delta)?;
        self.move_bound += Self::grouped_frobenius(delta);
        Ok(())
    }

    /// The current certified upper bound. This is not claimed to be the exact spectral norm
    /// between refreshes; it is the last Gram bound plus the exact sum of move bounds.
    pub(crate) fn upper(&self) -> Rat {
        &self.gram_bound + &self.move_bound
    }

    /// A certified Frobenius upper bound computed directly from one grouped dyadic array.
    pub(crate) fn grouped_frobenius(array: &EpochArray) -> Rat {
        Self::try_grouped_frobenius(array).expect("a valid legacy grouped array has its scalar square")
    }
    /// Native rational transient arithmetic may refuse its declared resource
    /// preflight. Propagate that refusal instead of panicking or forging a norm.
    pub(super) fn try_grouped_frobenius(array:&EpochArray)->Result<Rat,HnnError>{
        let squared=array.dot(array)?.scalar_ratio()?;
        Ok(if squared.is_zero(){Rat::zero()}else{root_ceiling(&squared)})
    }

    /// Exact scalar cache words for the epoch-law checkpoint. These are the last
    /// aeon-close Gram bound and the accumulated actual-move bound, respectively.
    pub(crate) fn checkpoint_words(&self) -> (usize, usize, &Rat, &Rat) {
        (self.rows, self.columns, &self.gram_bound, &self.move_bound)
    }

    /// Restore the cache only when its shape, nonnegative scalar bounds, and exact
    /// inertia certificate cover the represented grouped map. The baseline/drift split
    /// itself is preserved.
    pub(crate) fn from_checkpoint(
        rows: usize,
        columns: usize,
        gram_bound: Rat,
        move_bound: Rat,
        map: &EpochArray,
    ) -> Result<Self, HnnError> {
        let cache = Self {
            rows,
            columns,
            gram_bound,
            move_bound,
        };
        cache.admit_shape(map)?;
        if cache.gram_bound.is_negative() || cache.move_bound.is_negative() {
            return Err(HnnError::Unadmitted {
                reason: "an epoch spectral checkpoint has nonnegative bounds",
            });
        }
        if !upper_covers_grouped_map(map, &cache.upper())? {
            return Err(HnnError::Unadmitted {
                reason: "an epoch spectral checkpoint must certify its complete grouped map",
            });
        }
        Ok(cache)
    }

    fn admit_shape(&self, array: &EpochArray) -> Result<(), HnnError> {
        if (array.rows, array.columns) != (self.rows, self.columns) {
            return Err(HnnError::Unadmitted {
                reason: "an epoch spectral reading must keep its declared map shape",
            });
        }
        Ok(())
    }
}

/// Check `upper^2 I - WᵀW` or `upper^2 I - WWᵀ` with exact integer inertia.
/// The input and smaller certificate form both stay in grouped integer coordinates.
fn upper_covers_grouped_map(map: &EpochArray, upper: &Rat) -> Result<bool, HnnError> {
    if upper.is_negative() {
        return Ok(false);
    }
    let (rows, columns) = (map.rows, map.columns);
    let extent = rows.min(columns);
    if extent == 0 {
        return Ok(true);
    }
    let lines: Vec<Vec<BigInt>> = if rows <= columns {
        map.values.chunks(columns).map(<[BigInt]>::to_vec).collect()
    } else {
        (0..columns)
            .map(|column| {
                (0..rows)
                    .map(|row| map.values[row * columns + column].clone())
                    .collect()
            })
            .collect()
    };
    let mut gram = vec![vec![BigInt::zero(); extent]; extent];
    for i in 0..extent {
        for j in i..extent {
            let value = integer_dot(&lines[i], &lines[j]);
            gram[i][j] = value.clone();
            gram[j][i] = value;
        }
    }

    let exponent = 2usize
        .checked_mul(map.exponent as usize)
        .ok_or(HnnError::Unadmitted {
            reason: "an epoch spectral checkpoint exponent exceeds its exact chart",
        })?;
    let numerator = upper.numer();
    let denominator = upper.denom();
    let diagonal = numerator * numerator << exponent;
    let denominator_squared = denominator * denominator;
    let form: Vec<Vec<BigInt>> = (0..extent)
        .map(|i| {
            (0..extent)
                .map(|j| {
                    let mut entry = -(&denominator_squared * &gram[i][j]);
                    if i == j {
                        entry += &diagonal;
                    }
                    entry
                })
                .collect()
        })
        .collect();
    Ok(integer_positive_semidefinite(form))
}

/// Reuse the existing exact Gram/inertia certificate on the grouped array's integer face. The
/// face has 16 significant bits by the deposition owner's scalar certificate, and its discarded
/// tail is bounded by the matrix's Frobenius radius. No retained coordinate is rounded.
fn grouped_spectral_bound(array: &EpochArray) -> Result<Rat, HnnError> {
    let (rows, columns) = (array.rows, array.columns);
    if rows == 0 || columns == 0 {
        return Ok(Rat::zero());
    }
    let Some(widest) = array
        .values
        .iter()
        .filter(|value| !value.is_zero())
        .map(BigInt::bits)
        .max()
    else {
        return Ok(Rat::zero());
    };
    let face_exponent = i64::try_from(widest).map_err(|_| HnnError::Unadmitted {
        reason: "the grouped spectral face exponent exceeds its exact scalar chart",
    })? - 16;
    let (face, exact) = integer_face(&array.values, face_exponent);
    let unit = dyadic(face_exponent - i64::from(array.exponent));

    // As in holon::deposition::spectral_norm, use the smaller Gram and the Schur product as the
    // sound fallback. Rayleigh/power iteration only guesses candidates; exact inertia accepts one.
    let lines: Vec<Vec<BigInt>> = if rows <= columns {
        face.chunks(columns).map(<[BigInt]>::to_vec).collect()
    } else {
        (0..columns)
            .map(|column| {
                (0..rows)
                    .map(|row| face[row * columns + column].clone())
                    .collect()
            })
            .collect()
    };
    let extent = lines.len();
    let mut gram = vec![vec![BigInt::zero(); extent]; extent];
    for i in 0..extent {
        for j in i..extent {
            let value = integer_dot(&lines[i], &lines[j]);
            gram[j][i] = value.clone();
            gram[i][j] = value;
        }
    }

    let mut column_sums = vec![BigInt::zero(); columns];
    let mut row_widest = BigInt::zero();
    for row in face.chunks(columns) {
        let mut sum = BigInt::zero();
        for (total, value) in column_sums.iter_mut().zip(row) {
            let magnitude = value.abs();
            sum += &magnitude;
            *total += magnitude;
        }
        row_widest = row_widest.max(sum);
    }
    let schur_upper =
        Rat::from_integer(column_sums.into_iter().max().unwrap_or_default() * row_widest);

    let start = (0..extent).max_by_key(|&i| gram[i][i].clone()).unwrap_or(0);
    let mut vector: Vec<BigInt> = (0..extent)
        .map(|i| {
            if i == start {
                BigInt::one()
            } else {
                BigInt::zero()
            }
        })
        .collect();
    for _ in 0..16 {
        let next: Vec<BigInt> = gram.iter().map(|row| integer_dot(row, &vector)).collect();
        let shift = next
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0)
            .saturating_sub(64);
        vector = next
            .into_iter()
            .map(|value| value >> shift as usize)
            .collect();
    }
    let applied: Vec<BigInt> = gram.iter().map(|row| integer_dot(row, &vector)).collect();
    let vector_norm = integer_dot(&vector, &vector);
    let diagonal = Rat::from_integer(gram[start][start].clone());
    let lower = if vector_norm.is_zero() {
        diagonal
    } else {
        Rat::new(integer_dot(&vector, &applied), vector_norm).max(diagonal)
    };

    let dominates = |lambda: &Rat| -> bool {
        let (numerator, denominator) = (lambda.numer(), lambda.denom());
        let form: Vec<Vec<BigInt>> = (0..extent)
            .map(|i| {
                (0..extent)
                    .map(|j| {
                        let mut entry = -(denominator * &gram[i][j]);
                        if i == j {
                            entry += numerator;
                        }
                        entry
                    })
                    .collect()
            })
            .collect();
        integer_positive_semidefinite(form)
    };

    let mut bound = schur_upper.clone();
    for raise in [-6i64, -4, -2, 0, 1, 2, 3, 4, 5, 6] {
        let candidate = significant(&(&lower * (Rat::one() + dyadic(raise))), 24, true);
        if candidate >= schur_upper {
            break;
        }
        if dominates(&candidate) {
            bound = candidate;
            break;
        }
    }
    // The Schur fallback is already an exact algebraic upper; confirm the same Gram is PSD at
    // that boundary when no sharper inertia candidate was accepted.
    if bound == schur_upper && !dominates(&bound) {
        return Err(HnnError::Unadmitted {
            reason: "the grouped spectral Gram failed its exact Schur upper check",
        });
    }

    let face_error = if exact {
        Rat::zero()
    } else {
        root_ceiling(&Rat::from_integer(
            BigInt::from(rows) * BigInt::from(columns),
        )) / Rat::from_integer(BigInt::from(2))
    };
    Ok((root_ceiling(&bound) + face_error) * unit)
}

/// Exact zero-negative inertia decision over grouped integer symmetric forms. A
/// positive diagonal pivot is removed by its positive-scaled Schur complement
/// `p*A - c*cᵀ`; a common positive gcd is cancelled after each step. Negative
/// diagonals fail immediately. If every remaining diagonal is zero, PSD requires
/// the entire remainder to be zero, which rejects the hyperbolic zero-diagonal case.
/// This is the integer-input equivalent of the exact rational inertia certificate.
fn integer_positive_semidefinite(mut matrix: Vec<Vec<BigInt>>) -> bool {
    if matrix.iter().any(|row| row.len() != matrix.len()) {
        return false;
    }
    for i in 0..matrix.len() {
        for j in 0..matrix.len() {
            if matrix[i][j] != matrix[j][i] {
                return false;
            }
        }
    }
    while !matrix.is_empty() {
        let extent = matrix.len();
        if (0..extent).any(|i| matrix[i][i].is_negative()) {
            return false;
        }
        let Some(pivot_index) = (0..extent).find(|&i| matrix[i][i].is_positive()) else {
            return matrix.iter().flatten().all(Zero::is_zero);
        };
        if pivot_index != 0 {
            matrix.swap(0, pivot_index);
            for row in &mut matrix {
                row.swap(0, pivot_index);
            }
        }
        let pivot = matrix[0][0].clone();
        let next_extent = extent - 1;
        if next_extent == 0 {
            return true;
        }
        let mut next = vec![vec![BigInt::zero(); next_extent]; next_extent];
        for i in 0..next_extent {
            for j in 0..next_extent {
                next[i][j] = &pivot * &matrix[i + 1][j + 1] - &matrix[i + 1][0] * &matrix[0][j + 1];
            }
        }
        let divisor = next
            .iter()
            .flatten()
            .fold(BigInt::zero(), |gcd, value| crate::ratio::gcd(&gcd, value));
        if divisor > BigInt::one() {
            for value in next.iter_mut().flatten() {
                *value /= &divisor;
            }
        }
        matrix = next;
    }
    true
}

/// Nearest integer coordinates on the deposition law's dyadic face. Ties move away from zero;
/// the exactness bit records whether the omitted face-radius term vanishes.
fn integer_face(values: &[BigInt], exponent: i64) -> (Vec<BigInt>, bool) {
    let mut exact = true;
    let rounded = values
        .iter()
        .map(|value| {
            if exponent <= 0 {
                return value << (-exponent) as usize;
            }
            let denominator = BigInt::one() << exponent as usize;
            let quotient = value / &denominator;
            let remainder = value - &quotient * &denominator;
            if remainder.is_zero() {
                return quotient;
            }
            exact = false;
            if remainder.abs() * 2u32 >= denominator {
                quotient + value.signum()
            } else {
                quotient
            }
        })
        .collect();
    (rounded, exact)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::linear::inertia::{SymmetricForm, inertia};

    fn array(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
        EpochArray::new(
            rows,
            columns,
            exponent,
            values.iter().copied().map(BigInt::from).collect(),
        )
        .unwrap()
    }

    fn inertia_oracle(matrix: &[Vec<BigInt>]) -> bool {
        let form = SymmetricForm::from_rows(
            matrix
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|value| Rat::from_integer(value.clone()))
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        inertia(&form).negative == 0
    }

    #[test]
    fn integer_psd_matches_exact_inertia_on_small_and_degenerate_forms() {
        let explicit = [
            vec![vec![BigInt::zero()]],
            vec![
                vec![BigInt::one(), BigInt::zero()],
                vec![BigInt::zero(), BigInt::zero()],
            ],
            vec![
                vec![BigInt::from(2), BigInt::from(2)],
                vec![BigInt::from(2), BigInt::from(2)],
            ],
            vec![
                vec![BigInt::zero(), BigInt::one()],
                vec![BigInt::one(), BigInt::zero()],
            ],
            vec![
                vec![BigInt::from(-1), BigInt::zero()],
                vec![BigInt::zero(), BigInt::from(2)],
            ],
            vec![
                vec![BigInt::one(), BigInt::from(2)],
                vec![BigInt::from(2), BigInt::one()],
            ],
        ];
        for matrix in explicit {
            assert_eq!(
                integer_positive_semidefinite(matrix.clone()),
                inertia_oracle(&matrix),
                "matrix {matrix:?}"
            );
        }

        // Exhaust every symmetric 2×2 form with entries in {-2,-1,0,1,2}.
        for a in -2i32..=2 {
            for b in -2i32..=2 {
                for c in -2i32..=2 {
                    let matrix = vec![
                        vec![BigInt::from(a), BigInt::from(b)],
                        vec![BigInt::from(b), BigInt::from(c)],
                    ];
                    assert_eq!(
                        integer_positive_semidefinite(matrix.clone()),
                        inertia_oracle(&matrix),
                        "matrix {matrix:?}"
                    );
                }
            }
        }

        // Exhaust every symmetric 3×3 form whose six independent entries are -1, 0, or 1.
        for mut code in 0usize..3usize.pow(6) {
            let mut values = [0i32; 6];
            for value in &mut values {
                *value = (code % 3) as i32 - 1;
                code /= 3;
            }
            let matrix = vec![
                vec![values[0].into(), values[1].into(), values[2].into()],
                vec![values[1].into(), values[3].into(), values[4].into()],
                vec![values[2].into(), values[4].into(), values[5].into()],
            ];
            assert_eq!(
                integer_positive_semidefinite(matrix.clone()),
                inertia_oracle(&matrix),
                "matrix {matrix:?}"
            );
        }

        let rectangular = vec![
            vec![1.into(), 2.into(), 3.into()],
            vec![4.into(), 0.into(), 1.into()],
        ];
        let gram: Vec<Vec<BigInt>> = rectangular
            .iter()
            .map(|left| {
                rectangular
                    .iter()
                    .map(|right| integer_dot(left, right))
                    .collect()
            })
            .collect();
        assert_eq!(
            integer_positive_semidefinite(gram.clone()),
            inertia_oracle(&gram)
        );
        let large = BigInt::one() << 2048usize;
        let large_form = vec![
            vec![&large * &large, &large * &large],
            vec![&large * &large, &large * &large],
        ];
        assert_eq!(
            integer_positive_semidefinite(large_form.clone()),
            inertia_oracle(&large_form)
        );
    }

    #[test]
    fn grouped_spectral_and_frobenius_bounds_match_small_exact_singular_values() {
        let row = array(1, 2, 0, &[3, 4]);
        let spectral = grouped_spectral_bound(&row).unwrap();
        assert!(&spectral * &spectral >= Rat::from_integer(25.into()));
        assert!(spectral < Rat::from_integer(6.into()));
        assert_eq!(
            EpochSpectral::grouped_frobenius(&row),
            Rat::from_integer(5.into())
        );

        let rectangular = array(2, 3, 0, &[3, 0, 0, 0, 4, 0]);
        let rectangular_bound = grouped_spectral_bound(&rectangular).unwrap();
        assert!(rectangular_bound >= Rat::from_integer(4.into()));
        assert!(rectangular_bound < Rat::from_integer(5.into()));
    }

    #[test]
    fn zero_shapes_dyadic_scaling_and_large_coordinates_remain_exact() {
        for zero in [
            array(0, 7, 0, &[]),
            array(3, 0, 0, &[]),
            array(2, 3, 0, &[0; 6]),
        ] {
            assert_eq!(grouped_spectral_bound(&zero).unwrap(), Rat::zero());
            assert_eq!(EpochSpectral::grouped_frobenius(&zero), Rat::zero());
        }

        let ordinary = array(1, 2, 0, &[3, 4]);
        let dyadic = array(1, 2, 1, &[6, 8]);
        assert_eq!(ordinary, dyadic);
        let ordinary_bound = grouped_spectral_bound(&ordinary).unwrap();
        assert_eq!(ordinary_bound, grouped_spectral_bound(&dyadic).unwrap());

        let half_scale = array(1, 2, 1, &[3, 4]);
        assert_eq!(
            grouped_spectral_bound(&half_scale).unwrap(),
            ordinary_bound / Rat::from_integer(2.into())
        );

        let wide = BigInt::one() << 4096usize;
        let huge = EpochArray::new(1, 1, 0, vec![wide.clone()]).unwrap();
        assert!(grouped_spectral_bound(&huge).unwrap() >= Rat::from_integer(wide));
    }

    #[test]
    fn triangle_bound_accumulates_actual_moves_and_refresh_replaces_the_drift() {
        let mut spectral = EpochSpectral::founded_zero(2, 1);
        spectral.refresh(&array(2, 1, 0, &[3, 4])).unwrap();
        let base = spectral.upper();
        assert!(&base * &base >= Rat::from_integer(25.into()));
        spectral.observe_move(&array(2, 1, 0, &[0, 12])).unwrap();
        assert_eq!(spectral.upper(), &base + Rat::from_integer(12.into()));

        let moved = array(2, 1, 0, &[3, 12]);
        spectral.refresh(&moved).unwrap();
        let upper = spectral.upper();
        assert!(&upper * &upper >= Rat::from_integer(153.into()));
        assert!(upper < Rat::from_integer(13.into()));
        assert_eq!(spectral.move_bound, Rat::zero());
    }

    #[test]
    fn checkpoint_cache_requires_full_inertia_certificate_and_preserves_valid_split() {
        let rank_one =
            EpochArray::new(2, 2, 0, vec![1.into(), 1.into(), 1.into(), 1.into()]).unwrap();
        assert!(EpochSpectral::from_checkpoint(2, 2, Rat::one(), Rat::zero(), &rank_one,).is_err());

        let preserved = EpochSpectral::from_checkpoint(
            2,
            2,
            Rat::from_integer(2.into()),
            Rat::one(),
            &rank_one,
        )
        .unwrap();
        let (rows, columns, gram_bound, move_bound) = preserved.checkpoint_words();
        assert_eq!((rows, columns), (2, 2));
        assert_eq!(gram_bound, &Rat::from_integer(2.into()));
        assert_eq!(move_bound, &Rat::one());
        assert_eq!(preserved.upper(), Rat::from_integer(3.into()));
    }
}
