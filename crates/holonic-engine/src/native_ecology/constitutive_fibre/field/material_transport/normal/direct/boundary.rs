//! Boundary codec material built on the normal law.
//!
//! This module contains the small, source-independent part of the incident-field
//! boundary contract.  In particular, the seed is a material seed: it is not derived
//! from a glyph ordinal or from an observed target.  The resident normal operator is
//! still the owner of the accumulated statistics and its GPU action.

use crate::dimensional_wave::ExactComplexWaveCurrent;
use crate::native_ecology::constitutive_fibre::ConstitutiveFibreError;
use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

/// A deterministic, persisted material seed.  `seed` is deliberately the only
/// source identity used by the constructor; changing a codec's labels cannot change
/// the initial geometry.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct BoundaryMaterialSeed {
    pub seed: u64,
    pub fractional_bits: u32,
}

impl BoundaryMaterialSeed {
    pub const fn new(seed: u64, fractional_bits: u32) -> Self {
        Self {
            seed,
            fractional_bits,
        }
    }

    /// Construct distinct nonzero dyadic columns for `E_in`, and the exact bootstrap
    /// rows for `R_text`.  The returned rows are `[2 e_s^*, -||e_s||²]`, including the
    /// homogeneous bias coordinate.  No m-by-m matrix is formed here.
    pub fn initial_maps(
        self,
        source_symbols: usize,
        local_complex: usize,
    ) -> Result<BoundaryMaterialMaps, ConstitutiveFibreError> {
        if source_symbols == 0 || local_complex == 0 || !(1..=120).contains(&self.fractional_bits) {
            return Err(ConstitutiveFibreError::Shape);
        }
        // Keep the bootstrap norm on the resident grain while making the seed
        // large enough to survive the first dyadic output rounding.
        let seed_bits = (self.fractional_bits / 2).min(8);
        let denominator = BigInt::from(1u8) << seed_bits;
        let mut state = self.seed | 1;
        let mut encoder = Vec::with_capacity(source_symbols);
        let mut decoder = Vec::with_capacity(source_symbols);
        for source in 0..source_symbols {
            let mut column = Vec::with_capacity(local_complex);
            // A xorshift stream is only a carrier initializer.  Its values never
            // inspect the source label and are retained exactly as dyadic rationals.
            for _ in 0..local_complex {
                state ^= state << 7;
                state ^= state >> 9;
                state ^= state << 8;
                let real = ((state as i64 & 0x3f) + 1) as i64;
                state = state.rotate_left(17);
                let imaginary = ((state as i64 & 0x3f) - 32) as i64;
                column.push(ExactComplexWaveCurrent::new(
                    Rat::new(real.into(), denominator.clone()),
                    Rat::new(imaginary.into(), denominator.clone()),
                ));
            }
            // Ensure columns remain nonzero even for a degenerate short stream.
            if column.iter().all(ExactComplexWaveCurrent::is_zero) {
                column[0] = ExactComplexWaveCurrent::new(
                    Rat::new(1.into(), denominator.clone()),
                    Rat::zero(),
                );
            }
            // Resolve the (rare but possible) finite-stream collision without
            // consulting a glyph value.  The perturbation is still dyadic and
            // belongs to the persisted material seed.
            while encoder.iter().any(|old| old == &column) {
                let bump = BigInt::from((source as u64).saturating_add(1));
                column[0].real += Rat::new(bump, denominator.clone());
            }
            let norm: Rat = column
                .iter()
                .map(ExactComplexWaveCurrent::norm_square)
                .sum();
            let mut row = column
                .iter()
                .map(|z| {
                    ExactComplexWaveCurrent::new(
                        Rat::from_integer(2.into()) * &z.real,
                        Rat::from_integer(BigInt::from(-2)) * &z.imaginary,
                    )
                })
                .collect::<Vec<_>>();
            row.push(ExactComplexWaveCurrent::new(-norm, Rat::zero()));
            decoder.push(row);
            encoder.push(column);
        }
        Ok(BoundaryMaterialMaps { encoder, decoder })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryMaterialMaps {
    /// Columns are indexed by source face: `encoder[s]` is `e_s`.
    pub encoder: Vec<Vec<ExactComplexWaveCurrent>>,
    /// Rows contain the local coordinates followed by the homogeneous bias.
    pub decoder: Vec<Vec<ExactComplexWaveCurrent>>,
}

impl BoundaryMaterialMaps {
    pub fn source_symbols(&self) -> usize {
        self.encoder.len()
    }
    pub fn local_complex(&self) -> usize {
        self.encoder.first().map_or(0, Vec::len)
    }

    pub fn validate_bootstrap(&self) -> Result<(), ConstitutiveFibreError> {
        if self.encoder.is_empty() || self.encoder.len() != self.decoder.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        for (column, row) in self.encoder.iter().zip(&self.decoder) {
            if row.len() != column.len() + 1 || column.iter().all(ExactComplexWaveCurrent::is_zero)
            {
                return Err(ConstitutiveFibreError::Shape);
            }
            let norm: Rat = column
                .iter()
                .map(ExactComplexWaveCurrent::norm_square)
                .sum();
            for (e, r) in column.iter().zip(&row[..column.len()]) {
                if r != &ExactComplexWaveCurrent::new(
                    Rat::from_integer(2.into()) * &e.real,
                    Rat::from_integer(BigInt::from(-2)) * &e.imaginary,
                ) {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
            }
            if row[column.len()] != ExactComplexWaveCurrent::new(-norm, Rat::zero()) {
                return Err(ConstitutiveFibreError::Uncertain);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn seed_is_independent_of_labels_and_bootstraps_margin_rows() {
        let seed = BoundaryMaterialSeed::new(0x8a5c_19d3, 12);
        let a = seed.initial_maps(9, 3).unwrap();
        let b = seed.initial_maps(9, 3).unwrap();
        assert_eq!(a, b);
        a.validate_bootstrap().unwrap();
        assert!(a.encoder.iter().all(|e| e.iter().any(|z| !z.is_zero())));
        assert!(a.encoder.windows(2).all(|w| w[0] != w[1]));
    }

    #[test]
    fn bootstrap_rows_have_the_exact_squared_distance_selection_margin() {
        let maps = BoundaryMaterialSeed::new(0x91, 16)
            .initial_maps(5, 3)
            .unwrap();
        for (target, e_target) in maps.encoder.iter().enumerate() {
            let score = |row: &[ExactComplexWaveCurrent], e: &[ExactComplexWaveCurrent]| {
                row[..e.len()]
                    .iter()
                    .zip(e)
                    .map(|(a, b)| a.multiply(b).real)
                    .sum::<Rat>()
                    + row[e.len()].real.clone()
            };
            for (other, e_other) in maps.encoder.iter().enumerate() {
                if target == other {
                    continue;
                }
                let margin =
                    score(&maps.decoder[target], e_target) - score(&maps.decoder[other], e_target);
                let expected: Rat = e_target
                    .iter()
                    .zip(e_other)
                    .map(|(a, b)| a.add(&b.negated()).norm_square())
                    .sum();
                assert_eq!(margin, expected);
                assert!(margin > Rat::zero());
            }
        }
    }

}
