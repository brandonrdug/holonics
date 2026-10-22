//! Checked exterior operands and an explicit host oracle for exact card aggregation.
//!
//! These adapters retain the producer's values. They introduce no face partition,
//! metric, deposition, or alternative record aggregation. The reference is the
//! existing `EpochFlow::from_records` law; selecting it is explicit, never a
//! fallback from a failed device operation.
use super::*;

/// One actual unit-weight producer record, with its exact grouped row divisors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochProducerRecordReading {
    pub feature: EpochSeriesReading,
    pub covector: EpochSeriesReading,
}

/// Exact aggregation at one locus; records can outnumber heard cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochRecordFlowReading {
    pub gram: EpochSeriesReading,
    pub covector: EpochSeriesReading,
    pub support: Vec<usize>,
    pub records: u64,
    pub heard_cells: u64,
    pub declared_cells: u64,
    pub partition_exponent: u32,
}

/// Preserve the actual producer samples using the native record adapter.
/// Receiving phase rows keep their declared odd period; no value is rounded.
pub fn epoch_record_operands(
    samples: &[Sample],
    phase_rows: &[usize],
    period: u64,
) -> Result<Vec<EpochProducerRecordReading>, HnnError> {
    samples
        .iter()
        .map(|sample| {
            let record = EpochRecord::from_sample_with_phase_rows(sample, phase_rows, period)?;
            Ok(EpochProducerRecordReading {
                feature: EpochSeriesReading::of(&record.feature),
                covector: EpochSeriesReading::of(&record.covector),
            })
        })
        .collect()
}

fn array(reading: &EpochSeriesReading) -> Result<EpochArray, HnnError> {
    if reading.numerical_denominator.is_some(){return Err(refused("device packing has no native rational statistics qualification"));}
    EpochArray::with_row_divisors(
        reading.rows,
        reading.columns,
        reading.exponent,
        reading.numerators.clone(),
        reading.row_odd_divisors.clone(),
    )
}

fn decode(records: &[EpochProducerRecordReading]) -> Result<Vec<EpochRecord>, HnnError> {
    records
        .iter()
        .map(|record| {
            Ok(EpochRecord {
                feature: array(&record.feature)?,
                covector: array(&record.covector)?,
            })
        })
        .collect()
}

/// Native admission only: no G, Gram, reference aggregation, or fallback runs.
#[allow(clippy::too_many_arguments)]
pub fn epoch_record_flow_admit(
    rows: usize,
    columns: usize,
    receiver_grain: u32,
    epoch_cells: u64,
    epoch: u64,
    heard_cells: u64,
    records: &[EpochProducerRecordReading],
) -> Result<u32, HnnError> {
    EpochFlow::admit_records(
        rows,
        columns,
        receiver_grain,
        epoch_cells,
        epoch,
        heard_cells,
        &decode(records)?,
    )
}

/// Canonicalize exact device output through the native array constructor.
/// This checks shape, ordered support, count metadata and grouped odd divisors;
/// it never computes an aggregate or substitutes a host-computed result. Device
/// arithmetic/status and l1 validation remain the executing backend's duty.
pub fn epoch_record_flow_canonicalize(
    mut reading: EpochRecordFlowReading,
) -> Result<EpochRecordFlowReading, HnnError> {
    let columns = reading.gram.columns;
    if columns == 0
        || reading.gram.rows != columns
        || reading.covector.rows == 0
        || reading.covector.columns != columns
        || reading.declared_cells == 0
        || reading.heard_cells > reading.declared_cells
        || (reading.heard_cells == 0 && reading.records != 0)
        || reading.support.iter().any(|&i| i >= columns)
        || reading.support.windows(2).any(|p| p[0] >= p[1])
    {
        return Err(refused(
            "a device epoch flow must keep its locus shape, support and crossing counts",
        ));
    }
    let gram = array(&reading.gram)?;
    if !gram.is_dyadic() {
        return Err(refused("a device epoch Gram must remain dyadic"));
    }
    let covector = array(&reading.covector)?;
    reading.gram = EpochSeriesReading::of(&gram);
    reading.covector = EpochSeriesReading::of(&covector);
    Ok(reading)
}

/// The explicit host oracle calls the existing native aggregation exactly once.
/// Zero and partial-final epochs keep that owner's admission rules.
#[allow(clippy::too_many_arguments)]
pub fn epoch_record_flow_reference(
    rows: usize,
    columns: usize,
    receiver_grain: u32,
    epoch_cells: u64,
    epoch: u64,
    heard_cells: u64,
    records: &[EpochProducerRecordReading],
) -> Result<EpochRecordFlowReading, HnnError> {
    let flow = EpochFlow::from_records(
        rows,
        columns,
        receiver_grain,
        epoch_cells,
        epoch,
        heard_cells,
        &decode(records)?,
    )?;
    Ok(EpochRecordFlowReading {
        gram: EpochSeriesReading::of(&flow.gram),
        covector: EpochSeriesReading::of(&flow.covector),
        support: flow.support,
        records: flow.records,
        heard_cells: flow.cells,
        declared_cells: flow.partition_cells,
        partition_exponent: flow.partition_exponent,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn device_record_boundary_preserves_partial_odd_rows_and_record_multiplicity() {
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![rat(1, 2), rat(-1, 4)],
            covector: vec![rat(3, 4), rat(-1, 22)],
            masses: None,
        };
        let samples = vec![sample; 3];
        let records = epoch_record_operands(&samples, &[1], 11).unwrap();
        let flow = epoch_record_flow_reference(2, 2, 6, 231, 4, 1, &records).unwrap();
        assert_eq!(
            epoch_record_flow_admit(2, 2, 6, 231, 4, 1, &records).unwrap(),
            flow.partition_exponent
        );
        assert_eq!(flow.records, 3);
        assert_eq!(flow.heard_cells, 1);
        assert_eq!(flow.declared_cells, 231);
        assert_eq!(flow.support, vec![0, 1]);
        assert_eq!(flow.covector.row_odd_divisors, vec![1, 11]);
        let native_records = samples
            .iter()
            .map(|s| EpochRecord::from_sample_with_phase_rows(s, &[1], 11).unwrap())
            .collect::<Vec<_>>();
        let native = EpochFlow::from_records(2, 2, 6, 231, 4, 1, &native_records).unwrap();
        assert_eq!(flow.gram, EpochSeriesReading::of(&native.gram));
        assert_eq!(flow.covector, EpochSeriesReading::of(&native.covector));
        assert_eq!(epoch_record_flow_canonicalize(flow.clone()).unwrap(), flow);
        let mut uncancelled = flow.clone();
        for series in [&mut uncancelled.gram, &mut uncancelled.covector] {
            series.exponent += 3;
            for numerator in &mut series.numerators {
                *numerator <<= 3usize;
            }
        }
        assert_eq!(epoch_record_flow_canonicalize(uncancelled).unwrap(), flow);
    }

    #[test]
    fn device_record_boundary_refuses_malformed_or_changed_producer_operands() {
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![Rat::one(), rat(1, 11)],
            masses: None,
        };
        let records = epoch_record_operands(std::slice::from_ref(&sample), &[1], 11).unwrap();
        let mut malformed = records.clone();
        malformed[0].feature.numerators.clear();
        assert!(epoch_record_flow_admit(2, 1, 6, 231, 0, 1, &malformed).is_err());
        malformed = records.clone();
        malformed[0].covector.row_odd_divisors[1] = 2;
        assert!(epoch_record_flow_admit(2, 1, 6, 231, 0, 1, &malformed).is_err());
        let mut outside = records.clone();
        outside[0].feature.numerators[0] = BigInt::from(2);
        assert!(epoch_record_flow_admit(2, 1, 6, 231, 0, 1, &outside).is_err());
        assert!(epoch_record_flow_admit(2, 1, 6, 231, 0, 0, &records).is_err());
        let mut weighted = sample;
        weighted.weight = rat(1, 2);
        assert!(epoch_record_operands(&[weighted], &[1], 11).is_err());
        let zero = epoch_record_flow_reference(2, 1, 6, 231, 0, 0, &[]).unwrap();
        assert_eq!(zero.records, 0);
        assert!(zero.support.is_empty());
        let mut bad_support = zero;
        bad_support.support = vec![0, 0];
        assert!(epoch_record_flow_canonicalize(bad_support).is_err());
    }
}
