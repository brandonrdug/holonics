//! Exact record-to-flow aggregation for one receiver epoch.
//!
//! Each heard record contributes its own unweighted `f fᵀ` and `g fᵀ` term. The
//! face partition is counted by heard cells elsewhere; records add no partitions.

use super::{EpochArray, EpochFlow, extent, partition_exponent, refused};
use crate::hnn::HnnError;
use crate::hnn::constitution::Sample;
use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Zero};

/// One locus's exact producer feature and the carried covector that reached it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochRecord {
    /// One row of producer features on that producer's shared dyadic lattice.
    pub(crate) feature: EpochArray,
    /// One column of the return's covector at this locus.
    pub(crate) covector: EpochArray,
}

impl EpochRecord {
    /// Preserve an existing unit-weight producer sample at the epoch boundary.
    /// The source's exact feature and descent covector must lie on dyadic lattices;
    /// this conversion adds no normalization, sign change, or partition.
    pub(crate) fn from_sample(sample: &Sample) -> Result<Self, HnnError> {
        if sample.weight != Rat::one() {
            return Err(refused(
                "an epoch record adapter accepts producer samples of exact unit weight only",
            ));
        }
        let exponent = sample
            .feature
            .iter()
            .chain(&sample.covector)
            .map(dyadic_exponent)
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .max()
            .unwrap_or(0);
        let feature = EpochArray::new(
            1,
            sample.feature.len(),
            exponent,
            scale_values(&sample.feature, exponent)?,
        )?;
        let covector = EpochArray::new(
            sample.covector.len(),
            1,
            exponent,
            scale_values(&sample.covector, exponent)?,
        )?;
        Ok(Self { feature, covector })
    }
}

fn dyadic_exponent(value: &Rat) -> Result<u32, HnnError> {
    let denominator = value.denom();
    let bits = denominator.bits();
    let exponent = denominator.trailing_zeros().ok_or_else(|| {
        refused("an epoch producer sample denominator must be an exact power of two")
    })?;
    if bits != exponent + 1 {
        return Err(refused(
            "an epoch producer sample denominator must be an exact power of two",
        ));
    }
    u32::try_from(exponent).map_err(|_| extent())
}

fn scale_values(values: &[Rat], exponent: u32) -> Result<Vec<BigInt>, HnnError> {
    values
        .iter()
        .map(|value| {
            let value_exponent = dyadic_exponent(value)?;
            if value_exponent > exponent {
                return Err(refused(
                    "an epoch producer sample uses its exact common dyadic exponent",
                ));
            }
            Ok(value.numer() << (exponent - value_exponent) as usize)
        })
        .collect()
}

impl EpochFlow {
    /// Aggregate the independently heard records at one locus. `epoch_cells` is
    /// the declared partition bound `k`; `heard_cells` is the actual (possibly
    /// partial-final) count. Records are exact unit-weight terms and may outnumber
    /// either count because record multiplicity creates no face partition.
    pub(crate) fn from_records(
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochRecord],
    ) -> Result<Self, HnnError> {
        if rows == 0 || columns == 0 {
            return Err(refused("an epoch record flow needs both locus ports"));
        }
        if epoch_cells == 0 {
            return Err(refused(
                "an epoch record flow needs its nonzero declared partition bound",
            ));
        }
        if heard_cells > epoch_cells {
            return Err(refused(
                "an epoch record flow cannot hear more cells than its declared bound",
            ));
        }
        let partition_exponent = partition_exponent(receiver_grain, epoch_cells, epoch)?;
        let records_count = u64::try_from(records.len()).map_err(|_| extent())?;
        let mut gram = EpochArray::zero(columns, columns)?;
        let mut covector = EpochArray::zero(rows, columns)?;
        let mut reached = vec![false; columns];

        for record in records {
            if (record.feature.rows, record.feature.columns) != (1, columns)
                || (record.covector.rows, record.covector.columns) != (rows, 1)
            {
                return Err(refused(
                    "an epoch record's feature row and covector column must meet its locus",
                ));
            }
            if record
                .feature
                .values
                .iter()
                .any(|value| !within_unit(value, record.feature.exponent))
            {
                return Err(refused(
                    "an epoch producer feature must have exact magnitude at most one",
                ));
            }

            let transpose = EpochArray::new(
                columns,
                1,
                record.feature.exponent,
                record.feature.values.clone(),
            )?;
            let record_gram = transpose.multiply(&record.feature)?;
            gram = gram.add(&record_gram)?;
            covector = covector.add(&record.covector.multiply(&record.feature)?)?;
            for (support, feature) in reached.iter_mut().zip(&record.feature.values) {
                *support |= !feature.is_zero();
            }
        }

        Ok(Self {
            gram,
            covector,
            support: reached
                .iter()
                .enumerate()
                .filter_map(|(column, reached)| reached.then_some(column))
                .collect(),
            partitions: Vec::new(),
            cells: heard_cells,
            records: records_count,
            partition_exponent,
            receiver_grain,
            epoch,
        })
    }
}

/// Decide `|n| ≤ 2^exponent` from the coordinate's own bits, without allocating a
/// denominator face whose width is unrelated to the actual coordinate.
fn within_unit(value: &BigInt, exponent: u32) -> bool {
    let magnitude = value.magnitude();
    let bits = magnitude.bits();
    let exponent = u64::from(exponent);
    bits <= exponent || (bits == exponent + 1 && magnitude.trailing_zeros() == Some(exponent))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    fn array(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
        EpochArray::new(
            rows,
            columns,
            exponent,
            values.iter().copied().map(BigInt::from).collect(),
        )
        .unwrap()
    }

    fn record(feature: EpochArray, covector: EpochArray) -> EpochRecord {
        EpochRecord { feature, covector }
    }

    #[test]
    fn record_multiplicity_sums_exact_signed_terms_without_extra_partitions() {
        let records = [
            record(array(1, 2, 1, &[2, 1]), array(2, 1, 0, &[2, -1])),
            record(array(1, 2, 1, &[-1, 2]), array(2, 1, 0, &[-2, 3])),
            record(array(1, 2, 1, &[1, 1]), array(2, 1, 0, &[0, -4])),
        ];
        let flow = EpochFlow::from_records(2, 2, 32, 2, 0, 2, &records).unwrap();

        assert_eq!(flow.cells, 2);
        assert_eq!(flow.records, 3);
        assert!(flow.records > flow.cells);
        assert!(flow.partitions.is_empty());
        assert_eq!(
            flow.partition_exponent,
            super::super::partition_exponent(32, 2, 0).unwrap()
        );
        assert_eq!(
            flow.gram,
            EpochArray::new(2, 2, 2, vec![6.into(), 1.into(), 1.into(), 6.into()],).unwrap()
        );
        assert_eq!(
            flow.covector,
            EpochArray::new(2, 2, 1, vec![6.into(), -2.into(), -9.into(), 1.into()],).unwrap()
        );
        assert_eq!(flow.support, vec![0, 1]);
    }

    #[test]
    fn unit_features_are_checked_exactly_and_shapes_are_owned_by_the_locus() {
        let exactly_unit = [record(array(1, 2, 1, &[2, -2]), array(2, 1, 0, &[1, 0]))];
        assert!(EpochFlow::from_records(2, 2, 32, 231, 0, 1, &exactly_unit).is_ok());

        let outside_unit = [record(array(1, 2, 0, &[2, 0]), array(2, 1, 0, &[1, 0]))];
        assert!(EpochFlow::from_records(2, 2, 32, 231, 0, 1, &outside_unit).is_err());

        let wrong_feature = [record(array(2, 1, 0, &[1, 0]), array(2, 1, 0, &[1, 0]))];
        assert!(EpochFlow::from_records(2, 2, 32, 231, 0, 1, &wrong_feature).is_err());

        let wrong_covector = [record(array(1, 2, 0, &[1, 0]), array(1, 1, 0, &[1]))];
        assert!(EpochFlow::from_records(2, 2, 32, 231, 0, 1, &wrong_covector).is_err());
    }

    #[test]
    fn zero_records_and_partial_final_epochs_keep_cell_and_record_counts_distinct() {
        let empty = EpochFlow::from_records(2, 3, 24, 231, 4, 1, &[]).unwrap();
        assert_eq!(empty.cells, 1);
        assert_eq!(empty.records, 0);
        assert!(empty.gram.is_zero());
        assert!(empty.covector.is_zero());
        assert!(empty.support.is_empty());
        assert!(empty.partitions.is_empty());

        let records = [
            record(array(1, 3, 0, &[1, 0, 0]), array(2, 1, 0, &[1, -1])),
            record(array(1, 3, 1, &[0, 1, 0]), array(2, 1, 0, &[0, 1])),
        ];
        let partial = EpochFlow::from_records(2, 3, 24, 231, 4, 7, &records).unwrap();
        assert_eq!(partial.cells, 7);
        assert_eq!(partial.records, 2);
        assert_eq!(
            partial.partition_exponent,
            super::super::partition_exponent(24, 231, 4).unwrap()
        );
        assert_eq!(partial.support, vec![0, 1]);

        assert!(EpochFlow::from_records(2, 3, 24, 0, 0, 0, &[]).is_err());
        assert!(EpochFlow::from_records(2, 3, 24, 5, 0, 6, &[]).is_err());
    }

    #[test]
    fn unit_check_handles_large_exponents_without_a_fixed_width_face() {
        let tiny = EpochArray::new(1, 1, 1_000_000, vec![BigInt::one()]).unwrap();
        assert!(within_unit(&tiny.values[0], tiny.exponent));
        assert!(within_unit(&BigInt::one() << 1_000_000usize, 1_000_000));
    }

    #[test]
    fn sample_adapter_preserves_unit_weight_dyadics_and_refuses_other_faces() {
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![
                Rat::new(1.into(), 2.into()),
                Rat::new((-1).into(), 4.into()),
            ],
            covector: vec![
                Rat::new(3.into(), 4.into()),
                Rat::new((-1).into(), 2.into()),
            ],
            masses: None,
        };
        let record = EpochRecord::from_sample(&sample).unwrap();
        assert_eq!(record.feature, array(1, 2, 2, &[2, -1]));
        assert_eq!(record.covector, array(2, 1, 2, &[3, -2]));

        let nonunit = Sample {
            weight: Rat::from_integer(2.into()),
            ..sample.clone()
        };
        assert!(EpochRecord::from_sample(&nonunit).is_err());

        let nondyadic = Sample {
            covector: vec![Rat::new(1.into(), 11.into()), Rat::zero()],
            ..sample
        };
        assert!(EpochRecord::from_sample(&nondyadic).is_err());
    }
}
