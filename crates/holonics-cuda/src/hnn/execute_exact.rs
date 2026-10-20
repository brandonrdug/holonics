//! Runtime-width stages of the actual executed word (#76).
//!
//! `y = A x` and its adjoint `A^T g` use the same immutable producing matrix.
//! Matrix entries remain exact dyadic coordinates; vector coordinates share an
//! exact positive denominator, including its odd part. The card computes every
//! product, signed sum, l1 bound, and nearest-point carry. Only admission, exact
//! coordinate rebasing and the existing ReturnPrecision policy run on the host.
//! The product buffers stay resident between the policy's image read and carry.
//!
//! This stage is consumed by `readout::{source,paired_source}`. It does not claim
//! that the legacy whole forward/reverse word's i64 arrays have been widened.

use core::ffi::c_void;

use holonics::ratio::Rat;
use num_bigint::{BigInt, Sign};
use num_traits::Signed;

use super::DeviceError;
use super::card::{Card, CardBuffer, Layout};
use crate::cuda::DeviceZeroable;

pub const APPLY_ENTRY: &str = "hnn_word_exact_apply";
pub const CARRY_ENTRY: &str = "hnn_word_exact_carry";

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

// SAFETY: all-zero metadata denotes canonical positive zero and an empty bound.
unsafe impl DeviceZeroable for Output {}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Status {
    status: u32,
    committed: u32,
    required_words: u64,
    failing_entry: u64,
}

fn invalid(clause: &'static str) -> DeviceError {
    DeviceError::Launch {
        entry: APPLY_ENTRY,
        clause,
    }
}

fn product(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_mul(b)
        .ok_or_else(|| invalid("the exact word stage fits its host extent"))
}

fn sum(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_add(b)
        .ok_or_else(|| invalid("the exact word stage fits its host extent"))
}

fn capacity(bits: u64) -> Result<usize, DeviceError> {
    usize::try_from(bits.div_ceil(64).max(1))
        .map_err(|_| invalid("the exact word limb count fits this host"))
}

fn encode(value: &BigInt, arena: &mut Vec<u64>) -> Result<Word, DeviceError> {
    let (sign, limbs) = value.to_u64_digits();
    let offset =
        u64::try_from(arena.len()).map_err(|_| invalid("the exact word arena fits its wire"))?;
    let size = u64::try_from(limbs.len())
        .map_err(|_| invalid("the exact word magnitude fits its wire"))?;
    arena.extend_from_slice(&limbs);
    Ok(Word {
        offset,
        size,
        negative: u32::from(sign == Sign::Minus),
        reserved: 0,
    })
}

fn decode(words: &[u64], size: u64, negative: u32) -> Result<BigInt, DeviceError> {
    let size =
        usize::try_from(size).map_err(|_| invalid("the exact word magnitude fits this host"))?;
    if size > words.len()
        || negative > 1
        || (size == 0 && negative != 0)
        || (size != 0 && words[size - 1] == 0)
    {
        return Err(invalid(
            "the exact word result is canonical and inside its staging capacity",
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

fn admitted(status: Status) -> Result<(), DeviceError> {
    if status.status == 0 && status.committed == 1 {
        Ok(())
    } else {
        Err(DeviceError::WordExact {
            status: status.status,
            required_words: status.required_words,
            failing_entry: status.failing_entry,
        })
    }
}

fn not_run() -> Status {
    Status {
        status: 4,
        committed: 0,
        required_words: 0,
        failing_entry: u64::MAX,
    }
}

fn read_output(
    card: &Card,
    arena: &CardBuffer<'_, u64>,
    metadata: &CardBuffer<'_, Output>,
    result: &CardBuffer<'_, Status>,
    magnitude_capacity: usize,
) -> Result<(Vec<BigInt>, Vec<BigInt>), DeviceError> {
    admitted(card.fetch(result)?[0])?;
    let words = card.fetch(arena)?;
    let meta = card.fetch(metadata)?;
    let mut values = Vec::with_capacity(meta.len());
    let mut bounds = Vec::with_capacity(meta.len());
    for (i, m) in meta.iter().enumerate() {
        if m.reserved != 0 {
            return Err(invalid("the exact word output carries no unknown flags"));
        }
        let at = product(product(i, 2)?, magnitude_capacity)?;
        let value = decode(
            &words[at..at + magnitude_capacity],
            m.value_size,
            m.negative,
        )?;
        let bound = decode(
            &words[at + magnitude_capacity..at + 2 * magnitude_capacity],
            m.bound_size,
            0,
        )?;
        if value.abs() > bound {
            return Err(invalid(
                "the exact word sum lies inside its actual l1 bound",
            ));
        }
        values.push(value);
        bounds.push(bound);
    }
    Ok((values, bounds))
}

/// Actual matrix coordinates, with no signed-word carrier ceiling. The same
/// producing values serve forward and transpose applications.
#[derive(Clone, Debug)]
pub struct ExactWordMatrix {
    pub rows: usize,
    pub columns: usize,
    pub exponent: u32,
    pub numerators: Vec<BigInt>,
}

impl ExactWordMatrix {
    fn admit(&self) -> Result<(), DeviceError> {
        if self.rows == 0
            || self.columns == 0
            || product(self.rows, self.columns)? != self.numerators.len()
        {
            return Err(invalid(
                "the exact producing matrix has its complete nonempty shape",
            ));
        }
        Ok(())
    }
}

/// A real resident application. Product values and their l1 bounds remain on
/// the card until the return's split has consumed them.
pub struct ExactWordStage<'c> {
    card: &'c Card,
    output: CardBuffer<'c, u64>,
    meta: CardBuffer<'c, Output>,
    result: CardBuffer<'c, Status>,
    count: usize,
    columns: usize,
    denominator: BigInt,
    bound_bits: u64,
    pub layout: Layout,
    pub magnitude_capacity: usize,
}

/// Integer coordinates on the declared transient lattice and the final exact
/// feedback remainders. Remainders have the same normalized units as the seeds.
#[derive(Clone, Debug)]
pub struct ExactWordCarry {
    pub coordinates: Vec<Vec<BigInt>>,
    pub remainders: Vec<Rat>,
    /// Actual sum of product magnitudes, shifted onto the split's numerator
    /// scale, plus the incoming remainder magnitude; vector-major.
    pub pre_split_numerator_l1_bounds: Vec<BigInt>,
    pub layout: Layout,
    pub magnitude_capacity: usize,
}

impl Card {
    /// Apply actual immutable producing operands on the card. No product or sum
    /// is evaluated on the host. The common vector denominator is exact.
    pub fn exact_word_stage<'c>(
        &'c self,
        matrix: &ExactWordMatrix,
        vectors: &[Vec<Rat>],
        transpose: bool,
    ) -> Result<ExactWordStage<'c>, DeviceError> {
        self.exact_word_stage_at_capacity(matrix, vectors, transpose, None)
    }

    fn exact_word_stage_at_capacity<'c>(
        &'c self,
        matrix: &ExactWordMatrix,
        vectors: &[Vec<Rat>],
        transpose: bool,
        forced_capacity: Option<usize>,
    ) -> Result<ExactWordStage<'c>, DeviceError> {
        matrix.admit()?;
        let inputs = if transpose {
            matrix.rows
        } else {
            matrix.columns
        };
        let outputs = if transpose {
            matrix.columns
        } else {
            matrix.rows
        };
        if vectors.is_empty() || vectors.iter().any(|v| v.len() != inputs) {
            return Err(invalid(
                "each exact word vector has the producing map's input width",
            ));
        }
        let flattened: Vec<Rat> = vectors.iter().flatten().cloned().collect();
        let (numerators, vector_denominator) = super::dyadic::integral(&flattened);
        let denominator = vector_denominator << matrix.exponent as usize;
        let matrix_bits = matrix
            .numerators
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0);
        let vector_bits = numerators.iter().map(BigInt::bits).max().unwrap_or(0);
        let reduction_bits = if inputs <= 1 {
            0
        } else {
            u64::from(usize::BITS - (inputs - 1).leading_zeros())
        };
        let bound_bits = matrix_bits
            .checked_add(vector_bits)
            .and_then(|b| b.checked_add(reduction_bits))
            .and_then(|b| b.checked_add(1))
            .ok_or_else(|| invalid("the exact map's l1 width fits its native carrier"))?;
        // A zero matrix still admits every immutable operand view. Width derives
        // from both inputs and the reduction bound, never from cancellation.
        let magnitude_capacity =
            forced_capacity.unwrap_or(capacity(bound_bits.max(matrix_bits).max(vector_bits))?);
        let mut arena = Vec::new();
        let matrix_words = matrix
            .numerators
            .iter()
            .map(|n| encode(n, &mut arena))
            .collect::<Result<Vec<_>, _>>()?;
        let vector_words = numerators
            .iter()
            .map(|n| encode(n, &mut arena))
            .collect::<Result<Vec<_>, _>>()?;
        let entries = product(vectors.len(), outputs)?;
        let layout = self.cooperative_layout(APPLY_ENTRY, entries, None, 0)?;
        let lanes = product(layout.grid.x as usize, layout.block.x as usize)?;
        let output_words = product(product(entries, 2)?, magnitude_capacity)?;
        let scratch_words = product(lanes, sum(product(magnitude_capacity, 7)?, 1)?)?;
        let needed = sum(
            sum(
                product(arena.len(), 8)?,
                product(sum(matrix_words.len(), vector_words.len())?, 24)?,
            )?,
            sum(
                sum(product(output_words, 8)?, product(entries, 24)?)?,
                product(scratch_words, 8)?,
            )?,
        )?;
        if sum(needed, 24)? > self.census().memory.free_bytes {
            return Err(invalid(
                "the complete exact map stage fits the card's reported free memory",
            ));
        }
        let input = self.upload(&arena)?;
        let matrix_buffer = self.upload(&matrix_words)?;
        let vector_buffer = self.upload(&vector_words)?;
        let output = self.zeroed::<u64>(output_words)?;
        let meta = self.zeroed::<Output>(entries)?;
        let scratch = self.zeroed::<u64>(scratch_words)?;
        let result = self.upload(&[not_run()])?;
        let mut input_ptr = input.device_ptr();
        let mut input_words = arena.len() as u64;
        let mut matrix_ptr = matrix_buffer.device_ptr();
        let mut vectors_ptr = vector_buffer.device_ptr();
        let mut rows_wire = matrix.rows as u64;
        let mut columns_wire = matrix.columns as u64;
        let mut count_wire = vectors.len() as u64;
        let mut transpose_wire = u32::from(transpose);
        let mut capacity_wire = magnitude_capacity as u64;
        let mut output_ptr = output.device_ptr();
        let mut output_words_wire = output_words as u64;
        let mut meta_ptr = meta.device_ptr();
        let mut scratch_ptr = scratch.device_ptr();
        let mut scratch_words_wire = scratch_words as u64;
        let mut result_ptr = result.device_ptr();
        macro_rules! p {
            ($x:ident) => {
                &mut $x as *mut _ as *mut c_void
            };
        }
        self.launch_cooperative(
            APPLY_ENTRY,
            &layout,
            &mut [
                p!(input_ptr),
                p!(input_words),
                p!(matrix_ptr),
                p!(vectors_ptr),
                p!(rows_wire),
                p!(columns_wire),
                p!(count_wire),
                p!(transpose_wire),
                p!(capacity_wire),
                p!(output_ptr),
                p!(output_words_wire),
                p!(meta_ptr),
                p!(scratch_ptr),
                p!(scratch_words_wire),
                p!(result_ptr),
            ],
        )?;
        admitted(self.fetch(&result)?[0])?;
        Ok(ExactWordStage {
            card: self,
            output,
            meta,
            result,
            count: vectors.len(),
            columns: outputs,
            denominator,
            bound_bits,
            layout,
            magnitude_capacity,
        })
    }
}

impl ExactWordStage<'_> {
    /// Read exact images for the existing seed-driven ReturnPrecision policy.
    /// The resident numerators remain the carry stage's inputs.
    pub fn images(&self) -> Result<Vec<Vec<Rat>>, DeviceError> {
        let (values, _) = read_output(
            self.card,
            &self.output,
            &self.meta,
            &self.result,
            self.magnitude_capacity,
        )?;
        Ok(values
            .chunks_exact(self.columns)
            .map(|row| {
                row.iter()
                    .map(|n| Rat::new(n.clone(), self.denominator.clone()))
                    .collect()
            })
            .collect())
    }

    /// Exact l1 sums of the actual producing products, before the transient split.
    pub fn numerator_l1_bounds(&self) -> Result<Vec<BigInt>, DeviceError> {
        Ok(read_output(
            self.card,
            &self.output,
            &self.meta,
            &self.result,
            self.magnitude_capacity,
        )?
        .1)
    }

    /// Carry the exact resident images in the declared order. The return uses
    /// reverse chronological order; each coordinate has its own remainder stream.
    pub fn carry(
        &self,
        transient: u32,
        levels: u32,
        reverse: bool,
    ) -> Result<ExactWordCarry, DeviceError> {
        let shift = transient.checked_add(levels).ok_or_else(|| {
            invalid("the normalized reverse source exponent fits its native carrier")
        })?;
        let bound_bits =
            self.bound_bits
                .checked_add(u64::from(shift))
                .and_then(|b| b.checked_add(2))
                .ok_or_else(|| invalid("the carried source's l1 width fits its native carrier"))?
                .max(self.denominator.bits().checked_add(2).ok_or_else(|| {
                    invalid("the carried denominator width fits its native carrier")
                })?);
        let magnitude_capacity = capacity(bound_bits)?;
        let entries = product(sum(self.count, 1)?, self.columns)?;
        let layout = self
            .card
            .cooperative_layout(CARRY_ENTRY, self.columns, None, 0)?;
        let lanes = product(layout.grid.x as usize, layout.block.x as usize)?;
        let output_words = product(product(entries, 2)?, magnitude_capacity)?;
        let scratch_words = product(lanes, sum(product(magnitude_capacity, 12)?, 1)?)?;
        let mut denominator_arena = Vec::new();
        let mut denominator_word = encode(&self.denominator, &mut denominator_arena)?;
        let needed = sum(
            sum(
                product(denominator_arena.len(), 8)?,
                product(output_words, 8)?,
            )?,
            sum(product(entries, 24)?, product(scratch_words, 8)?)?,
        )?;
        if sum(needed, 24)? > self.card.census().memory.free_bytes {
            return Err(invalid(
                "the complete exact carry stage fits the card's reported free memory",
            ));
        }
        let denominator = self.card.upload(&denominator_arena)?;
        let output = self.card.zeroed::<u64>(output_words)?;
        let meta = self.card.zeroed::<Output>(entries)?;
        let scratch = self.card.zeroed::<u64>(scratch_words)?;
        let result = self.card.upload(&[not_run()])?;
        let mut input_ptr = self.output.device_ptr();
        let mut input_words = self.output.len() as u64;
        let mut input_meta = self.meta.device_ptr();
        let mut input_result = self.result.device_ptr();
        let mut input_capacity = self.magnitude_capacity as u64;
        let mut denominator_ptr = denominator.device_ptr();
        let mut denominator_words = denominator_arena.len() as u64;
        let mut count_wire = self.count as u64;
        let mut columns_wire = self.columns as u64;
        let mut shift_wire = i64::from(shift);
        let mut reverse_wire = u32::from(reverse);
        let mut capacity_wire = magnitude_capacity as u64;
        let mut output_ptr = output.device_ptr();
        let mut output_words_wire = output_words as u64;
        let mut meta_ptr = meta.device_ptr();
        let mut scratch_ptr = scratch.device_ptr();
        let mut scratch_words_wire = scratch_words as u64;
        let mut result_ptr = result.device_ptr();
        macro_rules! p {
            ($x:ident) => {
                &mut $x as *mut _ as *mut c_void
            };
        }
        self.card.launch_cooperative(
            CARRY_ENTRY,
            &layout,
            &mut [
                p!(input_ptr),
                p!(input_words),
                p!(input_meta),
                p!(input_result),
                p!(input_capacity),
                p!(denominator_ptr),
                p!(denominator_words),
                p!(denominator_word),
                p!(count_wire),
                p!(columns_wire),
                p!(shift_wire),
                p!(reverse_wire),
                p!(capacity_wire),
                p!(output_ptr),
                p!(output_words_wire),
                p!(meta_ptr),
                p!(scratch_ptr),
                p!(scratch_words_wire),
                p!(result_ptr),
            ],
        )?;
        let (mut values, mut bounds) =
            read_output(self.card, &output, &meta, &result, magnitude_capacity)?;
        let remainders = values.split_off(product(self.count, self.columns)?);
        bounds.truncate(product(self.count, self.columns)?);
        let scale = &self.denominator << transient as usize;
        Ok(ExactWordCarry {
            coordinates: values
                .chunks_exact(self.columns)
                .map(<[_]>::to_vec)
                .collect(),
            remainders: remainders
                .into_iter()
                .map(|n| Rat::new(n, scale.clone()))
                .collect(),
            pre_split_numerator_l1_bounds: bounds,
            layout,
            magnitude_capacity,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hnn::chart::carry;
    use holonics::hnn::constitution::Lattice;
    use num_traits::{One, Zero};

    #[test]
    fn exact_word_wire_roundtrips_beyond_both_legacy_carriers() {
        assert_eq!(core::mem::size_of::<Word>(), 24);
        assert_eq!(core::mem::size_of::<Output>(), 24);
        assert_eq!(core::mem::size_of::<Status>(), 24);
        for value in [
            BigInt::zero(),
            BigInt::one() << 131usize,
            -(BigInt::one() << 513usize),
        ] {
            let mut arena = Vec::new();
            let wire = encode(&value, &mut arena).unwrap();
            assert_eq!(decode(&arena, wire.size, wire.negative).unwrap(), value);
        }
    }

    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn exact_producing_maps_and_reverse_carries_match_native_odd_and_wide_oracles() {
        let card = Card::open(0).unwrap();
        let matrix = ExactWordMatrix {
            rows: 3,
            columns: 2,
            exponent: 101,
            numerators: vec![
                (BigInt::one() << 101usize) + 3,
                -(BigInt::one() << 260usize),
                BigInt::from(-7),
                BigInt::one() << 101usize,
                BigInt::one() << 260usize,
                BigInt::from(11),
            ],
        };
        let gradients = vec![
            vec![
                Rat::new(1.into(), 11.into()),
                Rat::new((-3).into(), 22.into()),
                Rat::new(5.into(), 33.into()),
            ],
            vec![
                Rat::new((-2).into(), 33.into()),
                Rat::new(7.into(), 11.into()),
                Rat::new((-1).into(), 66.into()),
            ],
            vec![
                Rat::new(3.into(), 22.into()),
                Rat::new(1.into(), 33.into()),
                Rat::new((-5).into(), 11.into()),
            ],
        ];
        let expected: Vec<Vec<Rat>> = gradients
            .iter()
            .map(|gradient| {
                (0..matrix.columns)
                    .map(|column| {
                        (0..matrix.rows)
                            .map(|row| {
                                Rat::new(
                                    matrix.numerators[row * matrix.columns + column].clone(),
                                    BigInt::one() << matrix.exponent as usize,
                                ) * &gradient[row]
                            })
                            .sum()
                    })
                    .collect()
            })
            .collect();
        let stage = card.exact_word_stage(&matrix, &gradients, true).unwrap();
        assert_eq!(stage.images().unwrap(), expected);
        assert!(stage.magnitude_capacity > 4);
        let (_, vector_denominator) = super::super::dyadic::integral(
            &gradients.iter().flatten().cloned().collect::<Vec<_>>(),
        );
        let expected_bounds: Vec<BigInt> = gradients
            .iter()
            .flat_map(|gradient| {
                let vector_denominator = &vector_denominator;
                let matrix = &matrix;
                (0..matrix.columns).map(move |column| {
                    (0..matrix.rows)
                        .map(|row| {
                            (&matrix.numerators[row * matrix.columns + column]
                                * (gradient[row].numer()
                                    * (vector_denominator / gradient[row].denom())))
                            .abs()
                        })
                        .sum()
                })
            })
            .collect();
        assert_eq!(stage.numerator_l1_bounds().unwrap(), expected_bounds);
        for reverse in [false, true] {
            let lattice = Lattice::new(14);
            let levels = 7;
            let mut rem = vec![Rat::zero(); matrix.columns];
            let mut expected_coordinates = vec![Vec::new(); gradients.len()];
            let order: Vec<usize> = if reverse {
                (0..gradients.len()).rev().collect()
            } else {
                (0..gradients.len()).collect()
            };
            for i in order {
                let normalized: Vec<Rat> = expected[i]
                    .iter()
                    .map(|v| v * Rat::from_integer(BigInt::one() << levels))
                    .collect();
                expected_coordinates[i] = carry(&lattice, &normalized, &mut rem)
                    .iter()
                    .map(|v| {
                        (v * Rat::from_integer(BigInt::one() << lattice.exponent() as usize))
                            .to_integer()
                    })
                    .collect();
            }
            let actual = stage.carry(lattice.exponent(), levels, reverse).unwrap();
            assert_eq!(actual.coordinates, expected_coordinates);
            assert_eq!(actual.remainders, rem);
        }
        // Forward and transpose share precisely one producing matrix.
        let vectors = vec![vec![
            Rat::new(1.into(), 3.into()),
            Rat::new((-2).into(), 5.into()),
        ]];
        let forward = card
            .exact_word_stage(&matrix, &vectors, false)
            .unwrap()
            .images()
            .unwrap();
        let transpose = stage.images().unwrap();
        let left: Rat = forward[0]
            .iter()
            .zip(&gradients[0])
            .map(|(a, b)| a * b)
            .sum();
        let right: Rat = vectors[0]
            .iter()
            .zip(&transpose[0])
            .map(|(a, b)| a * b)
            .sum();
        assert_eq!(left, right);
        // Negative half ties go upward; the following phase receives the
        // remainder rather than independently rounding the same input again.
        let identity = ExactWordMatrix {
            rows: 1,
            columns: 1,
            exponent: 0,
            numerators: vec![BigInt::one()],
        };
        let ties = vec![
            vec![Rat::new((-1).into(), 2.into())],
            vec![Rat::new(1.into(), 2.into())],
            vec![Rat::new(1.into(), 3.into())],
            vec![Rat::new((-2).into(), 3.into())],
        ];
        let ties_stage = card.exact_word_stage(&identity, &ties, false).unwrap();
        let tied = ties_stage.carry(0, 0, false).unwrap();
        let mut tie_remainder = vec![Rat::zero()];
        let expected_ties: Vec<Vec<BigInt>> = ties
            .iter()
            .map(|seed| {
                carry(&Lattice::new(0), seed, &mut tie_remainder)
                    .iter()
                    .map(Rat::to_integer)
                    .collect()
            })
            .collect();
        assert_eq!(tied.coordinates, expected_ties);
        assert_eq!(tied.coordinates[0], vec![BigInt::zero()]);
        assert_eq!(tied.remainders, tie_remainder);
        // Exact cancellation cannot shrink the certified product width.
        let cancelling = ExactWordMatrix {
            rows: 1,
            columns: 2,
            exponent: 0,
            numerators: vec![BigInt::one() << 513usize, -(BigInt::one() << 513usize)],
        };
        let cancellation = card
            .exact_word_stage(
                &cancelling,
                &[vec![
                    Rat::from_integer(1.into()),
                    Rat::from_integer(1.into()),
                ]],
                false,
            )
            .unwrap();
        assert!(cancellation.images().unwrap()[0][0].is_zero());
        assert_eq!(
            cancellation.numerator_l1_bounds().unwrap(),
            vec![BigInt::one() << 514usize]
        );
        assert!(matches!(
            card.exact_word_stage_at_capacity(&matrix, &gradients, true, Some(1)),
            Err(DeviceError::WordExact { status: 1, .. })
        ));
        assert_eq!(
            card.exact_word_stage(&matrix, &gradients, true)
                .unwrap()
                .images()
                .unwrap(),
            expected
        );
    }
}
