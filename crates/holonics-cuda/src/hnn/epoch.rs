//! Exact producer-record aggregation on a resident cooperative grid (#76).
//!
//! The helical pair's actual reached records contribute `G = sum g f^T` and
//! `delta H = sum f f^T`. The host only admits and rebases their exact coordinates;
//! products, sums, l1 bounds and reached support are computed on the card. There is
//! no host aggregation fallback. This is an epoch component, not the complete
//! reception/forward/adjoint/certificate/publication circuit.

use core::ffi::c_void;

use holonics::hnn::constitution::{
    EpochProducerRecordReading, EpochRecordFlowReading, EpochSeriesReading,
    epoch_record_flow_admit, epoch_record_flow_canonicalize,
};
use num_bigint::{BigInt, Sign};
use num_traits::Signed;

use super::{Card, DeviceError, Layout};
use crate::cuda::DeviceZeroable;

pub const FLOW_ENTRY: &str = "hnn_epoch_flow";

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Word {
    offset: u64,
    size: u64,
    negative: u32,
    reserved: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Output {
    value_size: u64,
    bound_size: u64,
    negative: u32,
    reserved: u32,
}

// SAFETY: an all-zero Output is two empty unsigned magnitudes and canonical positive zero.
unsafe impl DeviceZeroable for Output {}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Status {
    status: u32,
    committed: u32,
    required_words: u64,
    failing_entry: u64,
}

/// Actual component work and bus traffic, beside the exact native result.
#[derive(Clone, Debug)]
pub struct EpochFlowExecution {
    pub flow: EpochRecordFlowReading,
    pub layout: Layout,
    pub magnitude_capacity: usize,
    pub numerator_l1_bounds: Vec<BigInt>,
    pub bytes_to_device: u64,
    pub bytes_from_device: u64,
    /// Initialization, input admission, and completed staging use three grid barriers.
    pub grid_barriers: u32,
}

fn invalid(clause: &'static str) -> DeviceError {
    DeviceError::Launch {
        entry: FLOW_ENTRY,
        clause,
    }
}

fn product(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_mul(b)
        .ok_or_else(|| invalid("the epoch surface fits its host extent"))
}

fn sum(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_add(b)
        .ok_or_else(|| invalid("the epoch surface fits its host extent"))
}

fn common_odd(a: u64, b: u64) -> Result<u64, DeviceError> {
    let (mut x, mut y) = (a, b);
    while y != 0 {
        (x, y) = (y, x % y);
    }
    (a / x)
        .checked_mul(b)
        .ok_or_else(|| invalid("the common odd row divisor fits its native carrier"))
}

fn encode(value: &BigInt, arena: &mut Vec<u64>) -> Result<Word, DeviceError> {
    let (sign, limbs) = value.to_u64_digits();
    let offset =
        u64::try_from(arena.len()).map_err(|_| invalid("the operand arena fits its wire"))?;
    let size =
        u64::try_from(limbs.len()).map_err(|_| invalid("the operand magnitude fits its wire"))?;
    arena.extend_from_slice(&limbs);
    Ok(Word {
        offset,
        size,
        negative: u32::from(sign == Sign::Minus),
        reserved: 0,
    })
}

fn decode(words: &[u64], size: u64, negative: u32) -> Result<BigInt, DeviceError> {
    let size = usize::try_from(size).map_err(|_| invalid("a returned magnitude fits this host"))?;
    if size > words.len()
        || negative > 1
        || (size == 0 && negative != 0)
        || (size != 0 && words[size - 1] == 0)
    {
        return Err(invalid(
            "a returned magnitude is canonical and inside its staged capacity",
        ));
    }
    let mut digits = Vec::with_capacity(product(size, 2)?);
    for &word in &words[..size] {
        digits.push(word as u32);
        digits.push((word >> 32) as u32);
    }
    Ok(BigInt::new(
        if negative == 0 {
            Sign::Plus
        } else {
            Sign::Minus
        },
        digits,
    ))
}

fn ceil_log2(value: usize) -> u64 {
    if value <= 1 {
        0
    } else {
        u64::from(usize::BITS - (value - 1).leading_zeros())
    }
}

impl Card {
    /// Compute the existing native record-to-flow law with actual card products and sums.
    /// Records may outnumber heard cells; they do not add a receiver partition.
    #[allow(clippy::too_many_arguments)]
    pub fn aggregate_epoch_records(
        &self,
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochProducerRecordReading],
    ) -> Result<EpochFlowExecution, DeviceError> {
        self.aggregate_epoch_records_at_capacity(
            rows,
            columns,
            receiver_grain,
            epoch_cells,
            epoch,
            heard_cells,
            records,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn aggregate_epoch_records_at_capacity(
        &self,
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochProducerRecordReading],
        test_capacity: Option<usize>,
    ) -> Result<EpochFlowExecution, DeviceError> {
        let partition_exponent = epoch_record_flow_admit(
            rows,
            columns,
            receiver_grain,
            epoch_cells,
            epoch,
            heard_cells,
            records,
        )?;
        let f_exp = records
            .iter()
            .map(|r| r.feature.exponent)
            .max()
            .unwrap_or(0);
        let g_exp = records
            .iter()
            .map(|r| r.covector.exponent)
            .max()
            .unwrap_or(0);
        let cov_exp = f_exp
            .checked_add(g_exp)
            .ok_or_else(|| invalid("the covector exponent fits its native carrier"))?;
        let gram_exp = f_exp
            .checked_mul(2)
            .ok_or_else(|| invalid("the Gram exponent fits its native carrier"))?;
        let mut divisors = vec![1u64; rows];
        for record in records {
            for (d, &next) in divisors.iter_mut().zip(&record.covector.row_odd_divisors) {
                *d = common_odd(*d, next)?;
            }
        }
        let mut arena = Vec::new();
        let mut features = Vec::with_capacity(product(records.len(), columns)?);
        let mut covectors = Vec::with_capacity(product(records.len(), rows)?);
        let (mut f_bits, mut g_bits) = (0u64, 0u64);
        for record in records {
            for n in &record.feature.numerators {
                let n = n << (f_exp - record.feature.exponent) as usize;
                f_bits = f_bits.max(n.bits());
                features.push(encode(&n, &mut arena)?);
            }
            for (i, n) in record.covector.numerators.iter().enumerate() {
                let n = (n * (divisors[i] / record.covector.row_odd_divisors[i]))
                    << (g_exp - record.covector.exponent) as usize;
                g_bits = g_bits.max(n.bits());
                covectors.push(encode(&n, &mut arena)?);
            }
        }
        // Each product is bounded before it runs; m, not the heard-cell bound,
        // bounds the sum of absolute terms even when cancellation makes G zero.
        let bound_bits = f_bits
            .checked_add(g_bits.max(f_bits))
            .and_then(|b| b.checked_add(ceil_log2(records.len())))
            .and_then(|b| b.checked_add(1))
            .ok_or_else(|| invalid("the reduction l1 width fits its native carrier"))?;
        let capacity = usize::try_from(bound_bits.div_ceil(64).max(1))
            .map_err(|_| invalid("the crossing limb count fits this host"))?;
        let capacity = test_capacity.unwrap_or(capacity);
        let g_entries = product(rows, columns)?;
        let entries = sum(g_entries, product(columns, columns)?)?;
        let layout = self.cooperative_layout(FLOW_ENTRY, entries.max(columns), None, 0)?;
        let lanes = product(layout.grid.x as usize, layout.block.x as usize)?;
        let output_words = product(product(entries, 2)?, capacity)?;
        let scratch_words = product(lanes, sum(product(capacity, 7)?, 1)?)?;
        let bytes_to_device = sum(
            product(arena.len(), 8)?,
            product(sum(features.len(), covectors.len())?, 24)?,
        )?;
        let bytes_from_device = sum(
            sum(product(output_words, 8)?, product(entries, 24)?)?,
            sum(product(columns, 4)?, 24)?,
        )?;
        let working_bytes = sum(
            sum(bytes_to_device, bytes_from_device)?,
            product(scratch_words, 8)?,
        )?;
        if working_bytes > self.census().memory.free_bytes {
            return Err(invalid(
                "the complete crossing surface fits the card's reported free memory",
            ));
        }
        let input = self.upload(&arena)?;
        let feature = self.upload(&features)?;
        let covector = self.upload(&covectors)?;
        let output = self.zeroed::<u64>(output_words)?;
        let meta = self.zeroed::<Output>(entries)?;
        let support = self.zeroed::<u32>(columns)?;
        let scratch = self.zeroed::<u64>(scratch_words)?;
        let result = self.upload(&[Status {
            status: 4,
            committed: 0,
            required_words: 0,
            failing_entry: u64::MAX,
        }])?;
        let mut input_ptr = input.device_ptr();
        let mut input_words = arena.len() as u64;
        let mut feature_ptr = feature.device_ptr();
        let mut covector_ptr = covector.device_ptr();
        let mut record_count = records.len() as u64;
        let mut rows_wire = rows as u64;
        let mut columns_wire = columns as u64;
        let mut capacity_wire = capacity as u64;
        let mut output_ptr = output.device_ptr();
        let mut output_words_wire = output_words as u64;
        let mut meta_ptr = meta.device_ptr();
        let mut support_ptr = support.device_ptr();
        let mut scratch_ptr = scratch.device_ptr();
        let mut scratch_words_wire = scratch_words as u64;
        let mut result_ptr = result.device_ptr();
        macro_rules! p {
            ($x:ident) => {
                &mut $x as *mut _ as *mut c_void
            };
        }
        self.launch_cooperative(
            FLOW_ENTRY,
            &layout,
            &mut [
                p!(input_ptr),
                p!(input_words),
                p!(feature_ptr),
                p!(covector_ptr),
                p!(record_count),
                p!(rows_wire),
                p!(columns_wire),
                p!(capacity_wire),
                p!(output_ptr),
                p!(output_words_wire),
                p!(meta_ptr),
                p!(support_ptr),
                p!(scratch_ptr),
                p!(scratch_words_wire),
                p!(result_ptr),
            ],
        )?;
        let status = self.fetch(&result)?[0];
        if status.status != 0 || status.committed != 1 {
            return Err(DeviceError::EpochFlow {
                status: status.status,
                required_words: status.required_words,
                failing_entry: status.failing_entry,
            });
        }
        let words = self.fetch(&output)?;
        let metadata = self.fetch(&meta)?;
        let reached = self.fetch(&support)?;
        if reached.iter().any(|&v| v > 1) {
            return Err(invalid("the reached support is a Boolean reading"));
        }
        let mut values = Vec::with_capacity(entries);
        let mut bounds = Vec::with_capacity(entries);
        for (i, m) in metadata.iter().enumerate() {
            if m.reserved != 0 {
                return Err(invalid("the returned integer ABI has no unknown flags"));
            }
            let offset = product(product(i, 2)?, capacity)?;
            let value = decode(&words[offset..offset + capacity], m.value_size, m.negative)?;
            let bound = decode(
                &words[offset + capacity..offset + 2 * capacity],
                m.bound_size,
                0,
            )?;
            if value.abs() > bound {
                return Err(invalid("each returned sum lies inside its actual l1 bound"));
            }
            values.push(value);
            bounds.push(bound);
        }
        let gram = EpochSeriesReading {
            numerical_denominator: None,
            rows: columns,
            columns,
            exponent: gram_exp,
            row_odd_divisors: vec![1; columns],
            numerators: values.split_off(g_entries),
        };
        let covector = EpochSeriesReading {
            numerical_denominator: None,
            rows,
            columns,
            exponent: cov_exp,
            row_odd_divisors: divisors,
            numerators: values,
        };
        let flow = epoch_record_flow_canonicalize(EpochRecordFlowReading {
            gram,
            covector,
            support: reached
                .iter()
                .enumerate()
                .filter_map(|(i, &v)| (v != 0).then_some(i))
                .collect(),
            records: records.len() as u64,
            heard_cells,
            declared_cells: epoch_cells,
            partition_exponent,
        })?;
        Ok(EpochFlowExecution {
            flow,
            layout,
            magnitude_capacity: capacity,
            numerator_l1_bounds: bounds,
            bytes_to_device: (bytes_to_device + 24) as u64,
            bytes_from_device: bytes_from_device as u64,
            grid_barriers: 3,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hnn::constitution::epoch_record_flow_reference;
    use num_traits::{One, Zero};

    fn series(
        rows: usize,
        columns: usize,
        exponent: u32,
        nums: Vec<BigInt>,
        divisors: Vec<u64>,
    ) -> EpochSeriesReading {
        EpochSeriesReading {
            numerical_denominator: None,
            rows,
            columns,
            exponent,
            numerators: nums,
            row_odd_divisors: divisors,
        }
    }

    fn fixture() -> Vec<EpochProducerRecordReading> {
        (0..3)
            .map(|i| EpochProducerRecordReading {
                feature: series(
                    1,
                    3,
                    131,
                    vec![
                        BigInt::one() << 130usize,
                        BigInt::from(i - 1),
                        BigInt::zero(),
                    ],
                    vec![1],
                ),
                covector: series(
                    2,
                    1,
                    3 + i as u32,
                    vec![(BigInt::one() << 260usize) + i, -BigInt::from(i + 1)],
                    vec![1, if i == 1 { 33 } else { 11 }],
                ),
            })
            .collect()
    }

    #[test]
    fn wire_sizes_and_exact_limb_roundtrip() {
        assert_eq!(core::mem::size_of::<Word>(), 24);
        assert_eq!(core::mem::size_of::<Output>(), 24);
        assert_eq!(core::mem::size_of::<Status>(), 24);
        for n in [
            BigInt::zero(),
            BigInt::one() << 131usize,
            -(BigInt::one() << 320usize),
        ] {
            let mut arena = Vec::new();
            let w = encode(&n, &mut arena).unwrap();
            assert_eq!(decode(&arena, w.size, w.negative).unwrap(), n);
        }
    }

    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn actual_grouped_epoch_records_match_native_flow_without_host_fallback() {
        let card = Card::open(0).unwrap();
        let records = fixture();
        for heard in [1, 2] {
            let expected = epoch_record_flow_reference(2, 3, 6, 2, 4, heard, &records).unwrap();
            let actual = card
                .aggregate_epoch_records(2, 3, 6, 2, 4, heard, &records)
                .unwrap();
            assert_eq!(actual.flow, expected);
            assert!(actual.magnitude_capacity > 2);
            assert!(
                actual
                    .numerator_l1_bounds
                    .iter()
                    .all(|n| n >= &BigInt::zero())
            );
            eprintln!(
                "actual_epoch_flow: records={} heard={} capacity={} bytes_to={} bytes_from={} barriers={} layout={:?}",
                records.len(),
                heard,
                actual.magnitude_capacity,
                actual.bytes_to_device,
                actual.bytes_from_device,
                actual.grid_barriers,
                actual.layout
            );
        }
        let empty = card.aggregate_epoch_records(2, 3, 6, 2, 4, 0, &[]).unwrap();
        assert_eq!(
            empty.flow,
            epoch_record_flow_reference(2, 3, 6, 2, 4, 0, &[]).unwrap()
        );
        let mut wide = records.clone();
        for record in &mut wide {
            record.feature.columns = 37;
            record.feature.numerators.resize(37, BigInt::zero());
        }
        let actual = card
            .aggregate_epoch_records(2, 37, 6, 2, 4, 1, &wide)
            .unwrap();
        assert_eq!(
            actual.flow,
            epoch_record_flow_reference(2, 37, 6, 2, 4, 1, &wide).unwrap()
        );
        assert!(
            actual.layout.grid.x > 1,
            "this control must exercise a real multi-block grid"
        );
        let mut forged = actual.layout;
        forged.grid.x += 1;
        assert!(matches!(
            card.launch_cooperative(FLOW_ENTRY, &forged, &mut []),
            Err(DeviceError::Launch { .. })
        ));
        assert!(matches!(
            card.aggregate_epoch_records_at_capacity(2, 3, 6, 2, 4, 1, &records, Some(1)),
            Err(DeviceError::EpochFlow { status: 1, .. })
        ));
        // A failed staging read cannot contaminate the next crossing.
        let after = card
            .aggregate_epoch_records(2, 3, 6, 2, 4, 1, &records)
            .unwrap();
        assert_eq!(
            after.flow,
            epoch_record_flow_reference(2, 3, 6, 2, 4, 1, &records).unwrap()
        );
    }
}
