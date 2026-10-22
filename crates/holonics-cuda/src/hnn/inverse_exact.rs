//! Runtime-width inverse residual, Newton–Schulz refinement and certificate (#76).
//!
//! This realizes the existing `holonics::hnn::chart` law. Operator coordinates,
//! residuals, dot products, remainders and l1 bounds are exact signed limb spans;
//! chart coordinates retain the native signed64 admission. Device arithmetic
//! never falls back to a host inverse. The chart store still chooses starts by
//! the existing host law and commits only after every pair is certified.

use core::ffi::c_void;

use holonics::hnn::chart::{OperatorReading, OperatorWideReason};
use holonics::hnn::{ChartWords, HnnError};
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive};

use super::card::CardBuffer;
use super::dyadic::{common_exponent, coordinate, refused, value};
use super::{Card, DeviceError, Layout};
use crate::cuda::DeviceZeroable;

pub const INVERSE_EXACT_ENTRY: &str = "hnn_inverse_exact";

/// One exact dyadic operator, with its canonical common exponent and each row's
/// l1 coordinate bound. This is a transient representation of the native matrix.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactInverseOperator {
    pub width: usize,
    pub exponent: u32,
    pub numerators: Vec<BigInt>,
    pub row_l1_bounds: Vec<BigInt>,
}

impl ExactInverseOperator {
    /// The native owner's first representation-selection refusal, in exactly
    /// `chart::Operator::narrow` order. This reports provenance only; it neither
    /// computes nor substitutes a chart, residual, refinement or certificate.
    pub(crate) fn native_independent_reason(&self, exponent: u32) -> Option<OperatorWideReason> {
        if self.numerators.iter().any(|n| n.to_i128().is_none()) {
            Some(OperatorWideReason::Entry)
        } else if u64::from(self.exponent) + u64::from(exponent) > 126 {
            Some(OperatorWideReason::Scale)
        } else {
            None
        }
    }

    pub(crate) fn native_wide_reason(
        &self,
        words: &[i64],
        exponent: u32,
        newton: bool,
    ) -> Option<OperatorWideReason> {
        if let Some(reason) = self.native_independent_reason(exponent) {
            return Some(reason);
        }
        let max = BigInt::from(i128::MAX);
        let carrier = BigInt::one() << 127usize;
        let scale = BigInt::one() << (u64::from(self.exponent) + u64::from(exponent)) as usize;
        let qmax = words
            .iter()
            .map(|q| BigInt::from(*q).abs())
            .max()
            .unwrap_or_default();
        let product = self
            .row_l1_bounds
            .iter()
            .map(|row| row * &qmax)
            .max()
            .unwrap_or_default();
        if product >= carrier {
            return Some(OperatorWideReason::Product);
        }
        let residual = &scale + &product;
        if residual > max {
            return Some(OperatorWideReason::Residual);
        }
        if &residual * self.width > BigInt::from(u128::MAX) {
            return Some(OperatorWideReason::CertificateRow);
        }
        if newton {
            let twice = (&scale << 1usize) + product;
            if twice > max {
                return Some(OperatorWideReason::RefinementProduct);
            }
            let qrow = words
                .chunks(self.width)
                .map(|row| row.iter().map(|q| BigInt::from(*q).abs()).sum::<BigInt>())
                .max()
                .unwrap_or_default();
            let bound = qrow * twice;
            if bound >= carrier {
                return Some(OperatorWideReason::RefinementProduct);
            }
            if (&bound << 1usize) + &scale > max || (&scale << 1usize) > max {
                return Some(OperatorWideReason::Rounding);
            }
        }
        None
    }

    pub(crate) fn native_reading(
        &self,
        key: holonics::hnn::ChartKey,
        exponent: u32,
        reasons: &[OperatorWideReason],
    ) -> OperatorReading {
        OperatorReading {
            key,
            width: self.width,
            denominator_bits: u64::from(self.exponent) + 1,
            scale_bits: u64::from(self.exponent) + u64::from(exponent) + 1,
            entry_bits: self.numerators.iter().map(BigInt::bits).max().unwrap_or(0),
            wide_reasons: [
                OperatorWideReason::Entry,
                OperatorWideReason::Scale,
                OperatorWideReason::Product,
                OperatorWideReason::Residual,
                OperatorWideReason::CertificateRow,
                OperatorWideReason::RefinementProduct,
                OperatorWideReason::Rounding,
            ]
            .into_iter()
            .filter(|reason| reasons.contains(reason))
            .collect(),
        }
    }

    pub fn of(matrix: &ExactRatMatrix) -> Result<Self, HnnError> {
        let width = matrix.rows();
        let entries = width.checked_mul(width).ok_or(HnnError::CountOverflow)?;
        if width == 0 || matrix.columns() != width || matrix.entries().len() != entries {
            return Err(refused("a nonempty square exact inverse operator"));
        }
        let exponent = common_exponent(matrix.entries(), "an inverse operator on the dyadics")?;
        let numerators: Vec<_> = matrix
            .entries()
            .iter()
            .map(|n| coordinate(n, exponent).expect("admitted common dyadic exponent"))
            .collect();
        let row_l1_bounds = numerators
            .chunks(width)
            .map(|row| row.iter().map(Signed::abs).sum())
            .collect();
        Ok(Self {
            width,
            exponent,
            numerators,
            row_l1_bounds,
        })
    }

    pub fn row_norm(&self) -> Rat {
        value(
            self.row_l1_bounds.iter().max().cloned().unwrap_or_default(),
            self.exponent,
        )
    }

    /// Whether the operator and scale fit the old bounded128 ABI. That API's
    /// existing runtime l1 certificate still decides its product admission.
    pub(crate) fn bounded(&self, chart_exponent: u32) -> bool {
        let Some(shift) = self.exponent.checked_add(chart_exponent) else {
            return false;
        };
        if shift > super::word::INVERSE_EXPONENT_CEILING
            || self.numerators.iter().any(|n| n.to_i64().is_none())
        {
            return false;
        }
        // This path keeps the bounded carrier's existing runtime refusals. Its
        // API remains available; wide operator admission is selected separately.
        true
    }

    fn validate(&self) -> Result<(), DeviceError> {
        if self.width == 0
            || self.width.checked_mul(self.width) != Some(self.numerators.len())
            || self.row_l1_bounds.len() != self.width
            || self
                .numerators
                .chunks(self.width)
                .zip(&self.row_l1_bounds)
                .any(|(row, bound)| row.iter().map(Signed::abs).sum::<BigInt>() != *bound)
        {
            return Err(invalid(
                "an exact square operator has its actual row l1 bounds",
            ));
        }
        Ok(())
    }
}

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
    size: u64,
    negative: u32,
    reserved: u32,
}

// SAFETY: all-zero output is canonical positive zero with no unknown flags.
unsafe impl DeviceZeroable for Output {}

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct Status {
    status: u32,
    committed: u32,
    required_words: u64,
    failing_entry: u64,
}

/// Exact card results and actual work/bus evidence for one inverse operation.
#[derive(Clone, Debug)]
pub struct ExactInverseExecution {
    pub certificate: Rat,
    pub residual_numerators: Vec<BigInt>,
    pub residual_l1_bounds: Vec<BigInt>,
    /// `s = (next - old) * 2^S + remainder`, where `s = old * rho`.
    pub refinement_remainders: Vec<BigInt>,
    pub refinement_l1_bounds: Vec<BigInt>,
    pub next_chart: Option<ChartWords>,
    pub magnitude_capacity: usize,
    pub layout: Layout,
    pub bytes_to_device: u64,
    pub bytes_from_device: u64,
    pub grid_barriers: u32,
}

fn invalid(clause: &'static str) -> DeviceError {
    DeviceError::Launch {
        entry: INVERSE_EXACT_ENTRY,
        clause,
    }
}

fn product(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_mul(b)
        .filter(|n| *n <= isize::MAX as usize)
        .ok_or_else(|| invalid("the inverse surface fits its host extent"))
}

fn sum(a: usize, b: usize) -> Result<usize, DeviceError> {
    a.checked_add(b)
        .filter(|n| *n <= isize::MAX as usize)
        .ok_or_else(|| invalid("the inverse surface fits its host extent"))
}

fn encode(n: &BigInt, arena: &mut Vec<u64>) -> Result<Word, DeviceError> {
    let (sign, limbs) = n.to_u64_digits();
    let offset =
        u64::try_from(arena.len()).map_err(|_| invalid("the inverse arena fits its wire"))?;
    let size =
        u64::try_from(limbs.len()).map_err(|_| invalid("the inverse magnitude fits its wire"))?;
    arena.extend_from_slice(&limbs);
    Ok(Word {
        offset,
        size,
        negative: u32::from(sign == Sign::Minus),
        reserved: 0,
    })
}

fn decode(words: &[u64], output: Output) -> Result<BigInt, DeviceError> {
    let size = usize::try_from(output.size).map_err(|_| invalid("a returned inverse size fits"))?;
    if output.reserved != 0
        || output.negative > 1
        || size > words.len()
        || (size == 0 && output.negative != 0)
        || (size != 0 && words[size - 1] == 0)
    {
        return Err(invalid(
            "a returned inverse magnitude is canonical and within capacity",
        ));
    }
    let mut digits = Vec::with_capacity(product(size, 2)?);
    for &word in &words[..size] {
        digits.push(word as u32);
        digits.push((word >> 32) as u32);
    }
    Ok(BigInt::new(
        if output.negative == 0 {
            Sign::Plus
        } else {
            Sign::Minus
        },
        digits,
    ))
}

fn ceil_log2(n: usize) -> u64 {
    if n <= 1 {
        0
    } else {
        u64::from(usize::BITS - (n - 1).leading_zeros())
    }
}

/// Scratch and operator limbs stay on the card across a store's refinement.
pub(crate) struct ExactInverseWorkspace<'c> {
    card: &'c Card,
    width: usize,
    shift: u32,
    capacity: usize,
    layout: Layout,
    input: CardBuffer<'c, u64>,
    operators: CardBuffer<'c, Word>,
    scale: Word,
    output: CardBuffer<'c, u64>,
    meta: CardBuffer<'c, Output>,
    staged: CardBuffer<'c, i64>,
    scratch: CardBuffer<'c, u64>,
    status: CardBuffer<'c, Status>,
    pub(crate) octets: usize,
    pub(crate) launches: u64,
}

impl<'c> ExactInverseWorkspace<'c> {
    pub(crate) fn new(
        card: &'c Card,
        operator: &ExactInverseOperator,
        chart_exponent: u32,
    ) -> Result<Self, DeviceError> {
        Self::at_capacity(card, operator, chart_exponent, None)
    }

    fn at_capacity(
        card: &'c Card,
        operator: &ExactInverseOperator,
        chart_exponent: u32,
        test_capacity: Option<usize>,
    ) -> Result<Self, DeviceError> {
        operator.validate()?;
        let width = operator.width;
        let shift = operator
            .exponent
            .checked_add(chart_exponent)
            .ok_or_else(|| invalid("the inverse exponent fits its native carrier"))?;
        let entry_bits = operator
            .numerators
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0);
        // All possible native chart words have magnitude <= 2^63. Structural
        // bounds include diagonal scale, every absolute term, row sums and the
        // doubled rounding comparison. Cancellation cannot reduce this capacity.
        let dot_bits = entry_bits
            .checked_add(64)
            .and_then(|b| b.checked_add(ceil_log2(width)))
            .ok_or_else(|| invalid("the inverse l1 bit extent fits"))?;
        let residual_bits = dot_bits
            .max(u64::from(shift) + 1)
            .checked_add(1)
            .ok_or_else(|| invalid("the inverse residual bit extent fits"))?;
        let bits = residual_bits
            .checked_add(64)
            .and_then(|b| b.checked_add(ceil_log2(width)))
            .and_then(|b| b.checked_add(3))
            .ok_or_else(|| invalid("the inverse refinement bit extent fits"))?;
        let capacity = usize::try_from(bits.div_ceil(64).max(1))
            .map_err(|_| invalid("the inverse limb count fits this host"))?;
        let capacity = test_capacity.unwrap_or(capacity);
        let entries = product(width, width)?;
        let values = sum(product(entries, 4)?, 1)?;
        let layout = card.cooperative_layout(INVERSE_EXACT_ENTRY, entries, None, 0)?;
        let lanes = product(layout.grid.x as usize, layout.block.x as usize)?;
        let scratch_words = product(lanes, sum(product(capacity, 10)?, 1)?)?;
        let arena_words = operator.numerators.iter().try_fold(
            usize::try_from((u64::from(shift) + 1).div_ceil(64))
                .map_err(|_| invalid("the inverse scale limb count fits this host"))?,
            |words, n| {
                sum(
                    words,
                    usize::try_from(n.bits().div_ceil(64))
                        .map_err(|_| invalid("the inverse operand limb count fits this host"))?,
                )
            },
        )?;
        let output_words = product(values, capacity)?;
        let output_bytes = sum(product(output_words, 8)?, product(values, 16)?)?;
        let input_bytes = sum(product(arena_words, 8)?, product(entries, 24)?)?;
        let working = sum(
            sum(input_bytes, output_bytes)?,
            sum(product(entries, 8)?, sum(product(scratch_words, 8)?, 24)?)?,
        )?;
        if working > card.census().memory.free_bytes {
            return Err(invalid(
                "the complete inverse surface fits reported free card memory",
            ));
        }
        // Validate the complete arena before materializing its power-of-two
        // scale; an authored enormous exponent cannot allocate ahead of census.
        let mut arena = Vec::new();
        arena
            .try_reserve_exact(arena_words)
            .map_err(|_| invalid("the inverse input arena can be allocated"))?;
        let operators = operator
            .numerators
            .iter()
            .map(|n| encode(n, &mut arena))
            .collect::<Result<Vec<_>, _>>()?;
        let scale = encode(&(BigInt::one() << shift as usize), &mut arena)?;
        Ok(Self {
            card,
            width,
            shift,
            capacity,
            layout,
            input: card.upload(&arena)?,
            operators: card.upload(&operators)?,
            scale,
            output: card.zeroed(output_words)?,
            meta: card.zeroed(values)?,
            staged: card.zeroed(entries)?,
            scratch: card.zeroed(scratch_words)?,
            status: card.upload(&[Status {
                status: 16,
                committed: 0,
                required_words: 0,
                failing_entry: u64::MAX,
            }])?,
            octets: input_bytes + 24,
            launches: 0,
        })
    }

    fn run(
        &mut self,
        charts: &CardBuffer<'c, i64>,
        statuses: &CardBuffer<'c, u32>,
        source: usize,
        destination: Option<usize>,
    ) -> Result<Rat, DeviceError> {
        self.card.owns(charts)?;
        self.card.owns(statuses)?;
        let entries = product(self.width, self.width)?;
        for offset in [Some(source), destination].into_iter().flatten() {
            if offset
                .checked_add(entries)
                .is_none_or(|n| n > charts.len() || n > statuses.len())
            {
                return Err(invalid(
                    "the inverse chart and status blocks fit their buffers",
                ));
            }
        }
        let mut arena = self.input.device_ptr();
        let mut arena_words = self.input.len() as u64;
        let mut operators = self.operators.device_ptr();
        let mut scale = self.scale;
        let mut width = self.width as u64;
        let mut capacity = self.capacity as u64;
        let mut step = u32::from(destination.is_some());
        let mut chart = charts.device_ptr() + product(source, 8)? as u64;
        let mut chart_status = statuses.device_ptr() + product(source, 4)? as u64;
        let dest = destination.unwrap_or(source);
        let mut next = charts.device_ptr() + product(dest, 8)? as u64;
        let mut next_status = statuses.device_ptr() + product(dest, 4)? as u64;
        let mut output = self.output.device_ptr();
        let mut meta = self.meta.device_ptr();
        let mut staged = self.staged.device_ptr();
        let mut scratch = self.scratch.device_ptr();
        let mut scratch_words = self.scratch.len() as u64;
        let mut status = self.status.device_ptr();
        macro_rules! p {
            ($x:ident) => {
                &mut $x as *mut _ as *mut c_void
            };
        }
        self.card.launch_cooperative(
            INVERSE_EXACT_ENTRY,
            &self.layout,
            &mut [
                p!(arena),
                p!(arena_words),
                p!(operators),
                p!(scale),
                p!(width),
                p!(capacity),
                p!(step),
                p!(chart),
                p!(chart_status),
                p!(next),
                p!(next_status),
                p!(output),
                p!(meta),
                p!(staged),
                p!(scratch),
                p!(scratch_words),
                p!(status),
            ],
        )?;
        self.launches += 1;
        let status = self.card.fetch(&self.status)?[0];
        self.octets += 24;
        if status.status != 0 || status.committed != 1 {
            return Err(DeviceError::InverseExact {
                status: status.status,
                required_words: status.required_words,
                failing_entry: status.failing_entry,
            });
        }
        let index = product(entries, 4)?;
        let meta = self.card.fetch_range(&self.meta, index, 1)?[0];
        let limbs =
            self.card
                .fetch_range(&self.output, product(index, self.capacity)?, self.capacity)?;
        self.octets += 16 + 8 * self.capacity;
        let numerator = decode(&limbs, meta)?;
        if numerator.is_negative() {
            return Err(invalid("the inverse row norm is nonnegative"));
        }
        Ok(value(numerator, self.shift))
    }

    pub(crate) fn certify(
        &mut self,
        charts: &CardBuffer<'c, i64>,
        statuses: &CardBuffer<'c, u32>,
        offset: usize,
    ) -> Result<Rat, DeviceError> {
        self.run(charts, statuses, offset, None)
    }

    pub(crate) fn refine(
        &mut self,
        charts: &CardBuffer<'c, i64>,
        statuses: &CardBuffer<'c, u32>,
        source: usize,
        destination: usize,
    ) -> Result<(), DeviceError> {
        self.run(charts, statuses, source, Some(destination))
            .map(|_| ())
    }

    fn read_values(&mut self) -> Result<Vec<BigInt>, DeviceError> {
        let metadata = self.card.fetch(&self.meta)?;
        let words = self.card.fetch(&self.output)?;
        self.octets += metadata.len() * 16 + words.len() * 8;
        metadata
            .into_iter()
            .zip(words.chunks(self.capacity))
            .map(|(m, w)| decode(w, m))
            .collect()
    }
}

impl Card {
    /// Realize one exact residual/certificate and optionally the native rounded
    /// refinement. This control surface returns intermediates; the chart store's
    /// resident workspace reads only its certificate between refinement launches.
    pub fn inverse_exact(
        &self,
        operator: &ExactInverseOperator,
        chart: &ChartWords,
        refine: bool,
    ) -> Result<ExactInverseExecution, DeviceError> {
        self.inverse_exact_at_capacity(operator, chart, refine, None)
    }

    fn inverse_exact_at_capacity(
        &self,
        operator: &ExactInverseOperator,
        chart: &ChartWords,
        refine: bool,
        capacity: Option<usize>,
    ) -> Result<ExactInverseExecution, DeviceError> {
        if chart.rows() != operator.width
            || chart.columns() != operator.width
            || operator.width.checked_mul(operator.width) != Some(chart.words().len())
        {
            return Err(invalid(
                "the inverse chart has the exact operator's square shape",
            ));
        }
        let entries = chart.words().len();
        let mut words = chart.words().to_vec();
        words.resize(product(entries, 2)?, 0);
        let charts = self.upload(&words)?;
        let statuses = self.zeroed::<u32>(words.len())?;
        let mut workspace =
            ExactInverseWorkspace::at_capacity(self, operator, chart.exponent(), capacity)?;
        workspace.octets += words.len() * 8;
        let bytes_to_device = workspace.octets;
        let certificate = workspace.run(&charts, &statuses, 0, refine.then_some(entries))?;
        let mut values = workspace.read_values()?;
        values.pop(); // the certificate has already been admitted and decoded
        let refinement = values.split_off(2 * entries);
        let residual_numerators: Vec<_> = values.chunks_exact(2).map(|p| p[0].clone()).collect();
        let residual_l1_bounds: Vec<_> = values.chunks_exact(2).map(|p| p[1].clone()).collect();
        if residual_numerators
            .iter()
            .zip(&residual_l1_bounds)
            .any(|(n, b)| n.abs() > *b)
        {
            return Err(invalid("the residual lies inside its actual l1 bound"));
        }
        let (refinement_remainders, refinement_l1_bounds, next_chart) = if refine {
            let rem: Vec<_> = refinement.chunks_exact(2).map(|p| p[0].clone()).collect();
            let bounds: Vec<_> = refinement.chunks_exact(2).map(|p| p[1].clone()).collect();
            let scale = BigInt::one() << workspace.shift as usize;
            if rem
                .iter()
                .any(|r| (r << 1usize) < -&scale || (r << 1usize) >= scale)
            {
                return Err(invalid(
                    "the nearest split retains -half <= remainder < half",
                ));
            }
            let chart_words = self.fetch_range(&charts, entries, entries)?;
            workspace.octets += entries * 8;
            let coordinates: Vec<_> = chart_words.into_iter().map(BigInt::from).collect();
            (
                rem,
                bounds,
                Some(ChartWords::of_coordinates(
                    operator.width,
                    operator.width,
                    chart.exponent(),
                    &coordinates,
                )?),
            )
        } else {
            (Vec::new(), Vec::new(), None)
        };
        Ok(ExactInverseExecution {
            certificate,
            residual_numerators,
            residual_l1_bounds,
            refinement_remainders,
            refinement_l1_bounds,
            next_chart,
            magnitude_capacity: workspace.capacity,
            layout: workspace.layout,
            bytes_to_device: bytes_to_device as u64,
            bytes_from_device: (workspace.octets - bytes_to_device) as u64,
            grid_barriers: 6,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hnn::chart::{certificate, refine, transpose_start};
    use holonics::hnn::{ChartKey, ChartStart, WordLattice};
    use holonics::holon::element::contact_operator;
    use holonics::ratio::{integer, rat};
    use num_traits::Zero;

    fn contact() -> ExactRatMatrix {
        let identity = ExactRatMatrix::identity(2).unwrap();
        contact_operator(
            &identity,
            &identity.scaled(&rat(1, 4)),
            &identity.scaled(&rat(1, 4)),
            &Rat::new(BigInt::one(), BigInt::one() << 97usize),
            &Rat::one(),
        )
        .unwrap()
    }

    fn chart(width: usize, exponent: u32, words: &[i64]) -> ChartWords {
        ChartWords::of_coordinates(
            width,
            width,
            exponent,
            &words.iter().copied().map(BigInt::from).collect::<Vec<_>>(),
        )
        .unwrap()
    }

    /// Independent native rational products and native nearest-lattice split.
    fn oracle(matrix: &ExactRatMatrix, old: &ChartWords) -> (Vec<BigInt>, Vec<BigInt>, ChartWords) {
        let op = ExactInverseOperator::of(matrix).unwrap();
        let n = op.width;
        let scale = BigInt::one() << (op.exponent + old.exponent()) as usize;
        let mut rho = Vec::new();
        for i in 0..n {
            for j in 0..n {
                let sum: BigInt = (0..n)
                    .map(|k| &op.numerators[i * n + k] * old.words()[k * n + j])
                    .sum();
                rho.push(if i == j { &scale - sum } else { -sum });
            }
        }
        let mut remainders = Vec::new();
        let mut next = Vec::new();
        for i in 0..n {
            for j in 0..n {
                let s: BigInt = (0..n)
                    .map(|k| old.words()[i * n + k] * &rho[k * n + j])
                    .sum();
                let q = holonics::hnn::constitution::Lattice::new(0)
                    .div_rem(&Rat::new(s.clone(), scale.clone()))
                    .0;
                remainders.push(s - &q * &scale);
                next.push(BigInt::from(old.words()[i * n + j]) + q);
            }
        }
        (
            rho,
            remainders,
            ChartWords::of_coordinates(n, n, old.exponent(), &next).unwrap(),
        )
    }

    #[test]
    fn actual_s131_operator_admission_preserves_its_native_matrix() {
        let matrix = contact();
        let op = ExactInverseOperator::of(&matrix).unwrap();
        assert_eq!(op.width, 2);
        assert_eq!(op.exponent, 101);
        assert_eq!(op.numerators[0], (BigInt::one() << 101usize) + 19);
        assert_eq!(op.numerators[1], BigInt::zero());
        assert_eq!(op.row_norm(), matrix.entries()[0]);
        assert!(!op.bounded(30));
        assert!(super::super::dyadic::DyadicMatrix::of(&matrix, "old inverse words").is_err());
        for (coordinate, native) in op.numerators.iter().zip(matrix.entries()) {
            assert_eq!(value(coordinate.clone(), op.exponent), *native);
        }
        let key = ChartKey::Contact {
            contact: 0,
            carry: BigInt::from(-98),
        };
        let (_, native) =
            refine(key.clone(), &matrix, None, &WordLattice::new(30, 15, 20)).unwrap();
        assert_eq!(
            Some(op.native_reading(key, 30, &[OperatorWideReason::Scale])),
            native.operator
        );
        assert_eq!(core::mem::size_of::<Word>(), 24);
        assert_eq!(core::mem::size_of::<Output>(), 16);
        assert_eq!(core::mem::size_of::<Status>(), 24);
        for value in [
            BigInt::zero(),
            BigInt::one() << 131usize,
            -(BigInt::one() << 384usize),
        ] {
            let mut arena = Vec::new();
            let wire = encode(&value, &mut arena).unwrap();
            assert_eq!(
                decode(
                    &arena,
                    Output {
                        size: wire.size,
                        negative: wire.negative,
                        reserved: 0
                    }
                )
                .unwrap(),
                value
            );
        }
        let off = ExactRatMatrix::shaped(1, 1, vec![vec![rat(1, 3)]]).unwrap();
        assert!(ExactInverseOperator::of(&off).is_err());
        let mut malformed = op;
        malformed.row_l1_bounds[0] += 1;
        assert!(malformed.validate().is_err());
    }

    #[test]
    #[ignore = "needs the exclusive CUDA card; root launches bounded controls"]
    fn actual_s131_contact_matches_native_refinement_and_store_cold_then_warm() {
        let card = Card::open(0).unwrap();
        let matrix = contact();
        let op = ExactInverseOperator::of(&matrix).unwrap();
        let old = chart(2, 30, &[1 << 29, 0, 0, 1 << 29]);
        let expected = oracle(&matrix, &old);
        let actual = card.inverse_exact(&op, &old, true).unwrap();
        assert_eq!(actual.certificate, certificate(&matrix, &old).unwrap());
        assert_eq!(actual.residual_numerators, expected.0);
        assert_eq!(actual.refinement_remainders, expected.1);
        assert_eq!(actual.next_chart, Some(expected.2));
        let lattice = WordLattice::new(30, 15, 20);
        let key = ChartKey::Contact {
            contact: 0,
            carry: BigInt::from(-98),
        };
        let (native, reading) = refine(key.clone(), &matrix, None, &lattice).unwrap();
        let mut store = super::super::store::ChartStore::new(&card, &lattice).unwrap();
        let pairs = [super::super::store::Pair {
            key: key.clone(),
            matrix: &matrix,
            words: None,
        }];
        let first = store.refine(&pairs).unwrap();
        assert_eq!(first.readings[0], reading);
        assert_eq!(first.readings[0].certificate, reading.certificate);
        assert_eq!(first.readings[0].start, reading.start);
        assert_eq!(first.readings[0].steps, reading.steps);
        assert_eq!(store.continuing_charts().unwrap().get(&key), Some(&native));
        let second = store.refine(&pairs).unwrap();
        assert_eq!(second.readings[0].start, ChartStart::Warm);
        assert_eq!(second.readings[0].steps, 0);
        assert_eq!(store.continuing_charts().unwrap().get(&key), Some(&native));
        let (start, _) = transpose_start(&matrix, 30).unwrap();
        assert_eq!(start, old);

        // An authenticated scope can reuse the actual prepared ring proof.
        // Reuse performs only the device chart copy, with no inverse launch;
        // changing the operator invalidates that proof before execution.
        let mut ring_store = super::super::store::ChartStore::new(&card, &lattice).unwrap();
        let ring_pairs = [super::super::store::Pair {
            key: ChartKey::Ring(0),
            matrix: &matrix,
            words: None,
        }];
        let prepared = ring_store.refine(&ring_pairs).unwrap();
        let proof = ring_store.ring_preparations().unwrap();
        ring_store.reuse_ring_preparations(proof.clone());
        let before = ring_store.launches;
        let reused = ring_store.refine(&ring_pairs).unwrap();
        let mut expected = prepared.readings[0].clone();
        expected.start = ChartStart::Reused;
        expected.steps = 0;
        assert_eq!(reused.readings[0], expected);
        assert_eq!(ring_store.launches - before, 1);
        ring_store.reuse_ring_preparations(proof);
        let changed = matrix.scaled(&rat(2, 1));
        let invalidated = ring_store
            .refine(&[super::super::store::Pair {
                key: ChartKey::Ring(0),
                matrix: &changed,
                words: None,
            }])
            .unwrap();
        assert_ne!(invalidated.readings[0].start, ChartStart::Reused);
    }

    #[test]
    #[ignore = "needs the exclusive CUDA card; root launches bounded controls"]
    fn seven_limb_cancellation_and_signed_ties_keep_exact_bounds_and_remainders() {
        let card = Card::open(0).unwrap();
        let big: BigInt = (BigInt::one() << 384usize) + 17;
        let matrix = ExactRatMatrix::shaped(
            2,
            2,
            vec![
                vec![Rat::from_integer(big.clone()), Rat::from_integer(-&big)],
                vec![Rat::from_integer(-&big), Rat::from_integer(big.clone())],
            ],
        )
        .unwrap();
        let op = ExactInverseOperator::of(&matrix).unwrap();
        let old = chart(2, 0, &[1, 1, 1, 1]);
        let expected = oracle(&matrix, &old);
        let actual = card.inverse_exact(&op, &old, true).unwrap();
        assert!(actual.magnitude_capacity >= 7);
        assert_eq!(actual.residual_numerators, expected.0);
        assert_eq!(actual.refinement_remainders, expected.1);
        assert_eq!(actual.next_chart, Some(expected.2));
        assert_eq!(actual.certificate, Rat::one());
        assert_eq!(actual.refinement_l1_bounds, vec![BigInt::one(); 4]);
        assert_eq!(
            actual.residual_l1_bounds,
            vec![&big * 2 + 1, &big * 2, &big * 2, &big * 2 + 1]
        );
        for (a, x) in [
            (rat(3, 2), 1),
            (rat(1, 2), 1),
            (rat(3, 2), -1),
            (rat(-1, 2), -1),
        ] {
            let matrix = ExactRatMatrix::shaped(1, 1, vec![vec![a]]).unwrap();
            let op = ExactInverseOperator::of(&matrix).unwrap();
            let old = chart(1, 0, &[x]);
            let expected = oracle(&matrix, &old);
            let actual = card.inverse_exact(&op, &old, true).unwrap();
            assert_eq!(actual.certificate, certificate(&matrix, &old).unwrap());
            assert_eq!(actual.residual_numerators, expected.0);
            assert_eq!(actual.refinement_remainders, expected.1);
            assert_eq!(actual.next_chart, Some(expected.2));
        }
    }

    #[test]
    #[ignore = "needs the exclusive CUDA card; root launches bounded controls"]
    fn capacity_upstream_and_chart_word_refusals_leave_the_destination_unchanged() {
        let card = Card::open(0).unwrap();
        for (matrix, old, upstream, capacity, want) in [
            (
                ExactRatMatrix::shaped(
                    1,
                    1,
                    vec![vec![Rat::from_integer(BigInt::one() << 320usize)]],
                )
                .unwrap(),
                1,
                0,
                Some(1),
                1,
            ),
            (ExactRatMatrix::identity(1).unwrap(), 1, 8, None, 8),
            (
                ExactRatMatrix::shaped(1, 1, vec![vec![integer(0)]]).unwrap(),
                i64::MAX,
                0,
                None,
                4,
            ),
        ] {
            let op = ExactInverseOperator::of(&matrix).unwrap();
            let words = card.upload(&[old, 73]).unwrap();
            let statuses = card.upload(&[upstream, 77u32]).unwrap();
            let mut workspace =
                ExactInverseWorkspace::at_capacity(&card, &op, 0, capacity).unwrap();
            let error = workspace.refine(&words, &statuses, 0, 1).unwrap_err();
            match error {
                DeviceError::InverseExact {
                    status,
                    required_words,
                    ..
                } => {
                    assert_eq!(status, want);
                    if want == 1 {
                        assert!(required_words > 1);
                    }
                }
                other => panic!("unexpected inverse refusal: {other:?}"),
            }
            assert_eq!(card.fetch(&words).unwrap(), vec![old, 73]);
            assert_eq!(card.fetch(&statuses).unwrap(), vec![upstream, 77]);
        }
        // A forged negative-zero descriptor is refused by device admission,
        // before even an exactly zero product could conceal the malformed view.
        let op = ExactInverseOperator::of(&ExactRatMatrix::identity(1).unwrap()).unwrap();
        let words = card.upload(&[1i64, 73]).unwrap();
        let statuses = card.upload(&[0u32, 77]).unwrap();
        let mut workspace = ExactInverseWorkspace::new(&card, &op, 0).unwrap();
        card.write(
            &workspace.operators,
            0,
            &[Word {
                offset: 0,
                size: 0,
                negative: 1,
                reserved: 0,
            }],
        )
        .unwrap();
        assert!(matches!(
            workspace.refine(&words, &statuses, 0, 1),
            Err(DeviceError::InverseExact { status: 2, .. })
        ));
        assert_eq!(card.fetch(&words).unwrap(), vec![1, 73]);
        assert_eq!(card.fetch(&statuses).unwrap(), vec![0, 77]);
    }
}
