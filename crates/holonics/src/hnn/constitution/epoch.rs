//! One epoch's deposition: grouped exact series and the carried news `R = B - W H`.
//!
//! The computational object is the helical pair interaction. This owner changes a
//! constitution only at its receiver crossing; the helix, pair, faces and placement
//! remain the caller's. Precision is the receiver's tolerance partition, not an
//! authored machine width. Integer coordinates widen as their values require.

use super::*;

mod channel_ray;
mod checkpoint;
mod deposit;
pub(crate) mod device;
pub(crate) use deposit::{
    EpochCandidateScope, EpochDepositPhase, EpochReceivingRecord, ObservedNormalEpochStage,
    StagedEpochCandidate,
};
mod flow;
#[cfg(test)]
mod mixed_tests;
mod quantum_projection;
mod spectral;
pub(crate) use flow::EpochRecord;
use quantum_projection::QuantumProjection;
pub(crate) use spectral::EpochSpectral;

fn refused(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

fn extent() -> HnnError {
    ExactLinearError::ExtentOverflow.into()
}

/// The condition that stopped formation of an atomic epoch candidate. This is stage evidence,
/// never a finite comparison or a claim that the executed objective increased.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochStageCondition {
    NativeOwner,
    EpochAdmission,
    FlowContract,
    ReceivingSplit,
    FreshAlignment,
    SampleShape,
    ActualRayAlignment,
    ActualRayCurvature,
    JointNormalFall,
    JointTriangle,
    PumpTube,
    NonlinearFactorRay,
    SourceRefinementHalfCell,
    Lobe,
    CovectorScale,
    DeclaredFamily,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EpochStageValue {
    Ratio(Rat),
    Integer(BigInt),
    Index(usize),
    Indices(Vec<usize>),
    Exponent(u32),
    Carrier(Carrier),
    Step(CertifiedStep),
    Joint(JointReading),
    Tube(TubeClosure),
    Array(EpochArrayReading),
    /// Exact transient grouped coordinates, never installed in a continuing state.
    Series(EpochSeriesReading),
    JointDirection(EpochJointDirectionReading),
    Text(&'static str),
    /// The failing owner had not produced this operand, or its diagnostic could not be read.
    Unavailable(&'static str),
}

/// One operative exact reading, named at the guard that actually consumed it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochStageReading {
    pub name: &'static str,
    pub value: EpochStageValue,
}

/// Exterior evidence for the first failed guard of one staging attempt. No history is retained.
/// A missing locus/family means the native owner did not identify one; it is never inferred
/// from another family or from the receiving-only successor. Joint participants are separate
/// from a single failed family. Every such refusal precedes both seal formation and a probe.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EpochStageRefusal {
    pub phase: &'static str,
    pub condition: EpochStageCondition,
    pub required: &'static str,
    pub reason: String,
    pub locus: Option<Locus>,
    pub family: Option<Family>,
    pub participating_families: Vec<(Locus, Family)>,
    pub readings: Vec<EpochStageReading>,
    pub seal_formed: bool,
    pub finite_probe_executed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EpochStageAttempt {
    Whole,
    Joint,
    ReceivingOnly,
}

impl EpochStageRefusal {
    pub(crate) fn at(
        phase: &'static str,
        condition: EpochStageCondition,
        required: &'static str,
        locus: Option<Locus>,
        family: Option<Family>,
    ) -> Self {
        Self {
            phase,
            condition,
            required,
            reason: String::new(),
            locus,
            family,
            participating_families: Vec::new(),
            readings: Vec::new(),
            seal_formed: false,
            finite_probe_executed: false,
        }
    }
    pub(crate) fn read(mut self, name: &'static str, value: EpochStageValue) -> Self {
        self.readings.push(EpochStageReading { name, value });
        self
    }
    pub(crate) fn first(self, target: &mut Option<Self>) {
        if target.is_none() {
            *target = Some(self);
        }
    }

    /// Read the local certificate of this already refused, fixed ray. These values do not
    /// rescale a candidate or certify a joint ray, rounding, or an executed finite comparison.
    pub(crate) fn fixed_ray_step_diagnostic(mut self, step: &CertifiedStep) -> Self {
        self = self.read(
            "curvature_model",
            EpochStageValue::Text(
                "Gauss-Newton: score_curvature * propagation_gain * feature_moves; no executed second-variation/jet term",
            ),
        );
        self = self.read(
            "alignment_over_curvature",
            if step.curvature.is_zero() {
                EpochStageValue::Unavailable("zero curvature has no finite a/C ratio")
            } else {
                EpochStageValue::Ratio(&step.alignment / &step.curvature)
            },
        );
        self = self.read(
            "dyadic_diagnostic_scope",
            EpochStageValue::Text(
                "frozen local a/C and 1/c only; not a new candidate, endpoint reread, joint, tube or finite-probe admission",
            ),
        );
        match CertifiedStep::certify(&step.alignment, &step.curvature, &step.covector) {
            Ok(Some(local)) => self
                .read(
                    "largest_local_admissible_dyadic_k",
                    EpochStageValue::Integer(BigInt::from(local.exponent)),
                )
                .read(
                    "largest_local_admissible_dyadic",
                    EpochStageValue::Ratio(local.step),
                ),
            Ok(None) => self.read(
                "largest_local_admissible_dyadic_k",
                EpochStageValue::Unavailable("zero alignment certifies no moving step"),
            ),
            Err(_) => self.read(
                "largest_local_admissible_dyadic_k",
                EpochStageValue::Unavailable("the frozen local certificate refused its operands"),
            ),
        }
    }
}

#[derive(Debug)]
pub(crate) struct EpochStageFailure {
    pub(crate) error: HnnError,
    pub(crate) evidence: EpochStageRefusal,
    /// Transient same-batch preparation exists; not a retained or transferable certificate.
    pub(crate) normal_inputs_prepared: bool,
}

struct EpochStageTrace {
    phase: &'static str,
    locus: Option<Locus>,
    family: Option<Family>,
    evidence: Option<EpochStageRefusal>,
}
impl Default for EpochStageTrace {
    fn default() -> Self {
        Self {
            phase: "admission",
            locus: None,
            family: None,
            evidence: None,
        }
    }
}
impl EpochStageTrace {
    fn at(&mut self, phase: &'static str, locus: Option<Locus>, family: Option<Family>) {
        self.phase = phase;
        self.locus = locus;
        self.family = family;
    }
    fn failed(mut self, error: HnnError) -> EpochStageFailure {
        let mut evidence = self.evidence.take().unwrap_or_else(|| EpochStageRefusal::at(
            self.phase, EpochStageCondition::NativeOwner,
            "native owner admission; its unexported operative condition and failed family remain unknown",
            self.locus, self.family,
        ));
        // Preserve exact readings already carried by a typed native error. Opaque owners
        // keep their condition/attribution explicitly unknown rather than reconstructing it.
        match &error {
            HnnError::Shape {
                expected, found, ..
            } => {
                evidence.readings.push(EpochStageReading {
                    name: "expected",
                    value: EpochStageValue::Index(*expected),
                });
                evidence.readings.push(EpochStageReading {
                    name: "found",
                    value: EpochStageValue::Index(*found),
                });
            }
            HnnError::FactorStatistic { locus, statistic } => {
                evidence.locus = Some(*locus);
                evidence.readings.push(EpochStageReading {
                    name: "statistic",
                    value: EpochStageValue::Ratio(statistic.clone()),
                });
            }
            HnnError::ConstitutionBudget {
                bits,
                budget,
                commit,
                ..
            } => {
                for (name, value) in [("bits", *bits), ("budget", *budget), ("commit", *commit)] {
                    evidence.readings.push(EpochStageReading {
                        name,
                        value: EpochStageValue::Integer(BigInt::from(value)),
                    });
                }
            }
            HnnError::StaleDeposit { staged, published } => {
                evidence.readings.push(EpochStageReading {
                    name: "staged_commit",
                    value: EpochStageValue::Integer(BigInt::from(*staged)),
                });
                evidence.readings.push(EpochStageReading {
                    name: "published_commit",
                    value: EpochStageValue::Integer(BigInt::from(*published)),
                });
            }
            HnnError::Lattice { locus } | HnnError::ReleasedLocus { locus } => {
                evidence.locus = Some(*locus)
            }
            _ => {}
        }
        evidence.reason = error.to_string();
        EpochStageFailure {
            error,
            evidence,
            normal_inputs_prepared: false,
        }
    }
}

/// The caller's declared read budget, shared by all grouped laws in one native restore.
/// It bounds materialization before encoded exponents can allocate a denominator. Derived
/// dense views are charged too; this conservative read bound is distinct from the retained
/// constitution's final exact carrier census.
pub(super) struct CheckpointReadBudget {
    limit: u64,
    used: u64,
}

impl CheckpointReadBudget {
    pub(super) fn new(limit: u64) -> Self {
        Self { limit, used: 0 }
    }

    pub(super) fn check(&self, additional: u64) -> Result<(), HnnError> {
        let total = self.used.checked_add(additional).ok_or_else(extent)?;
        if total > self.limit {
            return Err(HnnError::ConstitutionBudget {
                bits: total,
                budget: self.limit,
                commit: 0,
                loci: Vec::new(),
            });
        }
        Ok(())
    }

    pub(super) fn charge(&mut self, additional: u64) -> Result<(), HnnError> {
        self.check(additional)?;
        self.used += additional;
        Ok(())
    }

    pub(super) fn admit_map_view(&mut self, map: &EpochArray) -> Result<(), HnnError> {
        let mut bits = 0u64;
        for (row, &divisor) in map.row_divisors.iter().enumerate() {
            let denominator = u64::from(map.exponent)
                .checked_add(u64::from(u64::BITS - divisor.leading_zeros()))
                .ok_or_else(extent)?;
            for numerator in &map.values[row * map.columns..(row + 1) * map.columns] {
                bits = bits
                    .checked_add(numerator.bits())
                    .and_then(|n| n.checked_add(1))
                    .and_then(|n| n.checked_add(denominator))
                    .ok_or_else(extent)?;
            }
        }
        self.charge(bits)
    }
}

fn ceil_log2_count(value: u64) -> u32 {
    if value <= 1 {
        0
    } else {
        u64::BITS - (value - 1).leading_zeros()
    }
}

/// The epoch's receiver-derived partition. `epoch` is counted from zero.
pub(crate) fn partition_exponent(
    receiver_grain: u32,
    cells: u64,
    epoch: u64,
) -> Result<u32, HnnError> {
    if cells == 0 {
        return Err(refused("an epoch partition needs its declared cell count"));
    }
    receiver_grain
        .checked_add(ceil_log2_count(cells))
        .and_then(|p| p.checked_add(1))
        .and_then(|p| p.checked_add(2 * ceil_log2_count(epoch.checked_add(1)?)))
        .ok_or_else(extent)
}

/// The any-length release bound. For `n>=1`, the dyadic blocks give
/// `sum 2^(-2 ceil(log2 n)) = 3/2`; multiplying by the epoch's cell bound
/// gives `3k / 2^(L_R+ceil(log2 k)+2) < 2^(-L_R)`.
pub(crate) fn lifetime_release_bound(
    receiver_grain: u32,
    cells: u64,
) -> Result<EpochArray, HnnError> {
    if cells == 0 {
        return Err(refused(
            "a lifetime release bound needs the epoch's cell count",
        ));
    }
    let exponent = receiver_grain
        .checked_add(ceil_log2_count(cells))
        .and_then(|p| p.checked_add(2))
        .ok_or_else(extent)?;
    EpochArray::new(1, 1, exponent, vec![BigInt::from(cells) * 3])
}

/// Grouped exact rows: one shared power of two, with the receiving phase rows'
/// declared odd period retained separately. W and H use only divisor-one rows.
/// Coordinates are never individually reduced. Content reduction is a shift.
// The grouped epoch coordinates extend the existing integral-chart owner.
// This alias introduces no independent retained array implementation.
pub(crate) type EpochArray = IntegralMatrix;

impl EpochArray {
    pub(crate) fn new(
        rows: usize,
        columns: usize,
        exponent: u32,
        values: Vec<BigInt>,
    ) -> Result<Self, HnnError> {
        Self::with_row_divisors(rows, columns, exponent, values, vec![1; rows])
    }

    pub(crate) fn with_row_divisors(
        rows: usize,
        columns: usize,
        exponent: u32,
        values: Vec<BigInt>,
        row_divisors: Vec<u64>,
    ) -> Result<Self, HnnError> {
        if rows.checked_mul(columns) != Some(values.len())
            || row_divisors.len() != rows
            || row_divisors.iter().any(|d| *d == 0 || d % 2 == 0)
        {
            return Err(refused(
                "an epoch array must fill its declared shape and odd row factors",
            ));
        }
        let numerator_l1_bound = values.iter().map(Signed::abs).sum();
        let mut array = Self {
            numerator_l1_bound,
            rows,
            columns,
            exponent,
            values,
            row_divisors,
            denominator: BigInt::one() << exponent as usize,
        };
        array.cancel();
        Ok(array)
    }

    pub(crate) fn zero(rows: usize, columns: usize) -> Result<Self, HnnError> {
        Self::new(
            rows,
            columns,
            0,
            vec![BigInt::zero(); rows.checked_mul(columns).ok_or_else(extent)?],
        )
    }

    fn cancel(&mut self) {
        let common = self
            .values
            .iter()
            .filter(|n| !n.is_zero())
            .map(|n| n.trailing_zeros().unwrap_or(0))
            .min();
        let Some(common) = common else {
            self.exponent = 0;
            self.denominator = BigInt::one();
            self.numerator_l1_bound = BigInt::zero();
            return;
        };
        let shift = common.min(u64::from(self.exponent)) as u32;
        if shift > 0 {
            for value in &mut self.values {
                *value >>= shift as usize;
            }
            self.exponent -= shift;
            self.numerator_l1_bound >>= shift as usize;
            self.denominator = BigInt::one() << self.exponent as usize;
        }
    }

    fn admit_grouped(&self) -> Result<(), HnnError> {
        if self.denominator != (BigInt::one() << self.exponent as usize) {
            return Err(refused(
                "epoch arithmetic requires an admitted grouped dyadic base, not a legacy common-rational chart",
            ));
        }
        Ok(())
    }

    fn same_shape(&self, other: &Self) -> Result<(), HnnError> {
        self.admit_grouped()?;
        other.admit_grouped()?;
        if (self.rows, self.columns) != (other.rows, other.columns) {
            return Err(refused("an epoch sum needs equal declared shapes"));
        }
        Ok(())
    }

    pub(crate) fn is_dyadic(&self) -> bool {
        self.denominator == (BigInt::one() << self.exponent as usize)
            && self.row_divisors.iter().all(|d| *d == 1)
    }

    pub(crate) fn add(&self, other: &Self) -> Result<Self, HnnError> {
        self.same_shape(other)?;
        let exponent = self.exponent.max(other.exponent);
        let divisors = self
            .row_divisors
            .iter()
            .zip(&other.row_divisors)
            .map(|(&a, &b)| common_odd(a, b))
            .collect::<Result<Vec<_>, _>>()?;
        let values = self
            .values
            .iter()
            .zip(&other.values)
            .enumerate()
            .map(|(i, (a, b))| {
                let row = i / self.columns;
                (a * (divisors[row] / self.row_divisors[row])
                    << (exponent - self.exponent) as usize)
                    + (b * (divisors[row] / other.row_divisors[row])
                        << (exponent - other.exponent) as usize)
            })
            .collect();
        Self::with_row_divisors(self.rows, self.columns, exponent, values, divisors)
    }

    pub(crate) fn subtract(&self, other: &Self) -> Result<Self, HnnError> {
        let negative = Self::with_row_divisors(
            other.rows,
            other.columns,
            other.exponent,
            other.values.iter().map(|v| -v).collect(),
            other.row_divisors.clone(),
        )?;
        self.add(&negative)
    }

    pub(crate) fn multiply(&self, other: &Self) -> Result<Self, HnnError> {
        self.admit_grouped()?;
        other.admit_grouped()?;
        if self.columns != other.rows {
            return Err(refused("an epoch product needs matching ports"));
        }
        let exponent = self
            .exponent
            .checked_add(other.exponent)
            .ok_or_else(extent)?;
        let right_divisor = other
            .row_divisors
            .iter()
            .try_fold(1, |a, &b| common_odd(a, b))?;
        let divisors = self
            .row_divisors
            .iter()
            .map(|d| d.checked_mul(right_divisor).ok_or_else(extent))
            .collect::<Result<Vec<_>, _>>()?;
        let mut values =
            vec![BigInt::zero(); self.rows.checked_mul(other.columns).ok_or_else(extent)?];
        for i in 0..self.rows {
            for k in 0..self.columns {
                let left = &self.values[i * self.columns + k];
                if left.is_zero() {
                    continue;
                }
                let factor = right_divisor / other.row_divisors[k];
                for j in 0..other.columns {
                    values[i * other.columns + j] +=
                        left * &other.values[k * other.columns + j] * factor;
                }
            }
        }
        Self::with_row_divisors(self.rows, other.columns, exponent, values, divisors)
    }

    fn dot(&self, other: &Self) -> Result<Self, HnnError> {
        self.same_shape(other)?;
        let divisors = self
            .row_divisors
            .iter()
            .zip(&other.row_divisors)
            .map(|(a, b)| a.checked_mul(*b).ok_or_else(extent))
            .collect::<Result<Vec<_>, _>>()?;
        let divisor = divisors.iter().try_fold(1, |a, &b| common_odd(a, b))?;
        let numerator = self
            .values
            .iter()
            .zip(&other.values)
            .enumerate()
            .map(|(i, (a, b))| a * b * (divisor / divisors[i / self.columns]))
            .sum();
        Self::with_row_divisors(
            1,
            1,
            self.exponent
                .checked_add(other.exponent)
                .ok_or_else(extent)?,
            vec![numerator],
            vec![divisor],
        )
    }

    fn half(&self) -> Result<Self, HnnError> {
        self.admit_grouped()?;
        Self::with_row_divisors(
            self.rows,
            self.columns,
            self.exponent.checked_add(1).ok_or_else(extent)?,
            self.values.clone(),
            self.row_divisors.clone(),
        )
    }

    pub(crate) fn scalar_product(&self, scalar: &Self) -> Result<Self, HnnError> {
        self.admit_grouped()?;
        scalar.admit_grouped()?;
        if (scalar.rows, scalar.columns) != (1, 1) {
            return Err(refused("an epoch scalar has one coordinate"));
        }
        let divisors = self
            .row_divisors
            .iter()
            .map(|d| d.checked_mul(scalar.row_divisors[0]).ok_or_else(extent))
            .collect::<Result<Vec<_>, _>>()?;
        Self::with_row_divisors(
            self.rows,
            self.columns,
            self.exponent
                .checked_add(scalar.exponent)
                .ok_or_else(extent)?,
            self.values.iter().map(|v| v * &scalar.values[0]).collect(),
            divisors,
        )
    }

    /// A transient integral chart for the existing scalar certificate. The
    /// retained arrays keep their separate magnitude/phase row factors.
    fn integral_chart(&self) -> Result<(Vec<BigInt>, BigInt), HnnError> {
        self.admit_grouped()?;
        let divisor = self
            .row_divisors
            .iter()
            .try_fold(1, |a, &b| common_odd(a, b))?;
        let values = self
            .values
            .iter()
            .enumerate()
            .map(|(i, v)| v * (divisor / self.row_divisors[i / self.columns]))
            .collect();
        Ok((values, BigInt::from(divisor) << self.exponent as usize))
    }

    pub(crate) fn scalar_ratio(&self) -> Result<Rat, HnnError> {
        self.admit_grouped()?;
        if (self.rows, self.columns) != (1, 1) {
            return Err(refused("an epoch scalar has one coordinate"));
        }
        Ok(Rat::new(
            self.values[0].clone(),
            BigInt::from(self.row_divisors[0]) << self.exponent as usize,
        ))
    }

    /// Boundary adapter only: ingest a native exact dyadic matrix without
    /// rounding or changing its chart. Grouped arrays remain the retained owner.
    pub(crate) fn from_dyadic_matrix(matrix: &ExactRatMatrix) -> Result<Self, HnnError> {
        let values: Vec<_> = matrix.entries().iter().cloned().collect();
        let exponents = values
            .iter()
            .map(|value| {
                let exponent = value.denom().trailing_zeros().ok_or_else(|| {
                    refused("a native epoch matrix needs a positive dyadic denominator")
                })?;
                if value.denom().bits() != exponent + 1 {
                    return Err(refused("a native epoch matrix must be exactly dyadic"));
                }
                u32::try_from(exponent).map_err(|_| extent())
            })
            .collect::<Result<Vec<_>, _>>()?;
        let exponent = exponents.iter().copied().max().unwrap_or(0);
        Self::new(
            matrix.rows(),
            matrix.columns(),
            exponent,
            values
                .iter()
                .zip(exponents)
                .map(|(v, e)| v.numer() << (exponent - e) as usize)
                .collect(),
        )
    }

    pub(crate) fn from_dyadic_scalar(value: &Rat) -> Result<Self, HnnError> {
        Self::from_dyadic_matrix(&ExactRatMatrix::shaped(1, 1, vec![vec![value.clone()]])?)
    }

    /// Materialize a boundary view for native forward operators. This is exact
    /// and does not repartition or mutate the retained grouped constitution.
    pub(crate) fn to_matrix(&self) -> Result<ExactRatMatrix, HnnError> {
        let rows = (0..self.rows)
            .map(|row| {
                let denominator = &self.denominator * self.row_divisors[row];
                (0..self.columns)
                    .map(|column| {
                        Rat::new(
                            self.values[row * self.columns + column].clone(),
                            denominator.clone(),
                        )
                    })
                    .collect()
            })
            .collect();
        Ok(ExactRatMatrix::shaped(self.rows, self.columns, rows)?)
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.values.iter().all(Zero::is_zero)
    }
    pub(crate) fn magnitude_limbs(&self) -> u64 {
        self.values
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0)
            .div_ceil(64)
    }
}

/// The only retained odd factors are declared powers of the same ring period;
/// unlike a rational coordinate sum this never creates or reduces a denominator.
fn common_odd(a: u64, b: u64) -> Result<u64, HnnError> {
    if a % b == 0 {
        Ok(a)
    } else if b % a == 0 {
        Ok(b)
    } else {
        Err(refused(
            "epoch row factors must share their declared receiving period",
        ))
    }
}

/// Exact series over one positive denominator, before the receiver's partition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochSeries {
    pub(crate) rows: usize,
    pub(crate) columns: usize,
    pub(crate) numerators: Vec<BigInt>,
    pub(crate) denominator: BigInt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochPartition {
    pub(crate) retained: EpochArray,
    /// `n*2^L = q*d + r`; the exact released value is `r/(d*2^L)`.
    pub(crate) remainder_numerators: Vec<BigInt>,
    pub(crate) denominator: BigInt,
    pub(crate) unit_exponent: u32,
}

impl EpochSeries {
    pub(crate) fn partition(&self, exponent: u32) -> Result<EpochPartition, HnnError> {
        if !self.denominator.is_positive()
            || self.rows.checked_mul(self.columns) != Some(self.numerators.len())
        {
            return Err(refused(
                "an epoch series needs its shape and positive common denominator",
            ));
        }
        let mut retained = Vec::with_capacity(self.numerators.len());
        let mut remainder_numerators = Vec::with_capacity(self.numerators.len());
        for numerator in &self.numerators {
            let scaled = numerator << exponent as usize;
            let quotient = &scaled / &self.denominator;
            let remainder = scaled - &quotient * &self.denominator;
            retained.push(quotient);
            remainder_numerators.push(remainder);
        }
        Ok(EpochPartition {
            retained: EpochArray::new(self.rows, self.columns, exponent, retained)?,
            remainder_numerators,
            denominator: self.denominator.clone(),
            unit_exponent: exponent,
        })
    }
}

/// Weighted identity-control operands retained only by the algebra tests.
/// Production records use `EpochRecord`: the receiving face is partitioned once
/// before the return, and every producer's metric weight is exactly one.
#[cfg(test)]
#[derive(Clone, Debug)]
pub(crate) struct EpochSample {
    pub(crate) feature: EpochArray,
    pub(crate) positive: EpochArray,
    pub(crate) foil: EpochSeries,
    pub(crate) metric_weight: EpochSeries,
}

#[derive(Clone, Debug)]
pub(crate) struct EpochFlow {
    pub(crate) gram: EpochArray,
    pub(crate) covector: EpochArray,
    pub(crate) support: Vec<usize>,
    pub(crate) partitions: Vec<EpochPartition>,
    pub(crate) cells: u64,
    /// Declared maximum heard faces, independent of producer record multiplicity.
    pub(crate) partition_cells: u64,
    pub(crate) records: u64,
    pub(crate) partition_exponent: u32,
    pub(crate) receiver_grain: u32,
    pub(crate) epoch: u64,
}

impl EpochFlow {
    /// The existing paired-port admission and orthogonal half-sum, applied to the
    /// whole epoch. Outside columns are never reached; the diagonal prior keeps
    /// them uncoupled, so the exact news update preserves the partial family too.
    pub(crate) fn paired(&self, symmetry: &PortSymmetry) -> Result<Self, HnnError> {
        let (rows, columns) = (self.covector.rows, self.covector.columns);
        if symmetry.rows().len() != rows || symmetry.columns().len() != columns {
            return Err(refused(
                "an epoch's paired family must match its normal locus",
            ));
        }
        if self.support.iter().any(|&j| j >= columns) {
            return Err(refused("a paired epoch names its declared columns only"));
        }
        if let Some(&class) = self
            .support
            .iter()
            .find(|&&j| symmetry.columns()[j].is_none())
        {
            return Err(HnnError::PairedOutside { class });
        }
        if (0..rows).any(|i| {
            self.covector.row_divisors[i] != self.covector.row_divisors[symmetry.rows()[i]]
        }) {
            return Err(refused(
                "a paired epoch must preserve its magnitude and phase row declarations",
            ));
        }
        let mut covector = Vec::with_capacity(rows * columns);
        for i in 0..rows {
            for j in 0..columns {
                let own = &self.covector.values[i * columns + j];
                covector.push(match symmetry.columns()[j] {
                    Some(partner) => {
                        own + &self.covector.values[symmetry.rows()[i] * columns + partner]
                    }
                    None => own << 1usize,
                });
            }
        }
        let mut gram = Vec::with_capacity(columns * columns);
        for i in 0..columns {
            for j in 0..columns {
                gram.push(
                    &self.gram.values[i * columns + j]
                        + &self.gram.values[symmetry.column(i) * columns + symmetry.column(j)],
                );
            }
        }
        let mut support = vec![false; columns];
        for &j in &self.support {
            support[j] = true;
            support[symmetry.column(j)] = true;
        }
        Ok(Self {
            gram: EpochArray::new(
                columns,
                columns,
                self.gram.exponent.checked_add(1).ok_or_else(extent)?,
                gram,
            )?,
            covector: EpochArray::with_row_divisors(
                rows,
                columns,
                self.covector.exponent.checked_add(1).ok_or_else(extent)?,
                covector,
                self.covector.row_divisors.clone(),
            )?,
            support: support
                .iter()
                .enumerate()
                .filter_map(|(j, &reached)| reached.then_some(j))
                .collect(),
            ..self.clone()
        })
    }

    #[cfg(test)]
    pub(crate) fn from_samples(
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        samples: &[EpochSample],
    ) -> Result<Self, HnnError> {
        if samples.len() as u64 > epoch_cells {
            return Err(refused("an epoch flow exceeds its declared cells"));
        }
        let exponent = partition_exponent(receiver_grain, epoch_cells, epoch)?;
        let mut gram = EpochArray::zero(columns, columns)?;
        let mut covector = EpochArray::zero(rows, columns)?;
        let mut reached = vec![false; columns];
        let mut partitions = Vec::with_capacity(2 * samples.len());
        for sample in samples {
            if (sample.feature.rows, sample.feature.columns) != (1, columns)
                || (sample.positive.rows, sample.positive.columns) != (rows, 1)
                || (sample.foil.rows, sample.foil.columns) != (rows, 1)
                || (sample.metric_weight.rows, sample.metric_weight.columns) != (1, 1)
            {
                return Err(refused("an epoch sample must meet its normal locus"));
            }
            // This is the feature bound used by the receiver's own lattice derivation.
            let unit = BigInt::one() << sample.feature.exponent as usize;
            if sample.feature.values.iter().any(|v| v.abs() > unit) {
                return Err(refused(
                    "the epoch receiver lattice requires features of magnitude at most one",
                ));
            }
            if sample
                .metric_weight
                .numerators
                .iter()
                .any(Signed::is_negative)
            {
                return Err(refused("an epoch metric weight must be nonnegative"));
            }
            let foil = sample.foil.partition(exponent)?;
            let metric = sample.metric_weight.partition(exponent)?;
            let mut outer = Vec::with_capacity(columns * columns);
            for a in &sample.feature.values {
                for b in &sample.feature.values {
                    outer.push(a * b);
                }
            }
            let feature_gram = EpochArray::new(
                columns,
                columns,
                sample.feature.exponent.checked_mul(2).ok_or_else(extent)?,
                outer,
            )?;
            gram = gram.add(&feature_gram.scalar_product(&metric.retained)?)?;
            let g = sample.positive.subtract(&foil.retained)?;
            covector = covector.add(&g.multiply(&sample.feature)?)?;
            for (seen, value) in reached.iter_mut().zip(&sample.feature.values) {
                *seen |= !value.is_zero();
            }
            partitions.extend([foil, metric]);
        }
        Ok(Self {
            gram,
            covector,
            support: reached
                .iter()
                .enumerate()
                .filter_map(|(j, p)| p.then_some(j))
                .collect(),
            partitions,
            cells: samples.len() as u64,
            partition_cells: epoch_cells,
            records: samples.len() as u64,
            partition_exponent: exponent,
            receiver_grain,
            epoch,
        })
    }
}

/// Retained normal-locus constitution. `B` is implicit: `B = W H + R`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochLaw {
    pub(crate) map: EpochArray,
    pub(crate) gram: EpochArray,
    pub(crate) news: EpochArray,
    pub(crate) receiver_grain: u32,
    pub(crate) map_lattice: u32,
    /// Source material alone may refine its dyadic representation at a crossing.
    /// R remains its only unabsorbed normal news; this is not another carry.
    pub(crate) source_refinement: bool,
    /// Number of absorbed batches, distinct from actual receiving ingress c.
    pub(crate) crossings: u64,
    /// This bound affects future certified gains, so a continuing checkpoint
    /// carries it with W/H/R rather than reconstructing a different schedule.
    pub(crate) spectral: EpochSpectral,
    symmetry: Option<PortSymmetry>,
}

#[derive(Clone, Debug)]
pub(crate) struct EpochDeposit {
    quantum_projection: Option<QuantumProjection>,
    pub(crate) successor: EpochLaw,
    pub(crate) step: EpochArray,
    pub(crate) fall: EpochArray,
    pub(crate) eta_numerator: BigInt,
    pub(crate) eta_denominator: BigInt,
    pub(crate) halvings: u64,
    pub(crate) direction: EpochArray,
    /// Actual D is this grouped numerator divided by this transient positive integer.
    pub(crate) direction_divisor: BigInt,
    pub(crate) joint_direction: Option<EpochJointDirectionReading>,
    pub(crate) shares: Vec<i64>,
}

/// Exact proposed direction only. The live normal owner retains W/H/R, never this wrapper.
struct EpochProposedDirection {
    numerator: EpochArray,
    divisor: BigInt,
    shares: Vec<i64>,
    joint: Option<EpochJointDirectionReading>,
}

/// The fresh news's certificate operands, formed before gamma or carried R is
/// read. Scalars are grouped dyadics too; the phase-three producer supplies c.
#[derive(Clone, Debug)]
pub(crate) struct EpochFresh {
    pub(crate) direction: EpochArray,
    pub(crate) alignment: EpochArray,
    pub(crate) moves: EpochArray,
    pub(crate) shares: Vec<i64>,
}

/// The current tightened certificate's scalar interface. The direction stays
/// one integer matrix over one denominator; only its scalar readings use Rat.
#[derive(Clone)]
pub(crate) struct EpochCertificateFace {
    unit: IntegralMatrix,
    alignment: Rat,
    moves: Rat,
    covector: Rat,
    unit_norms: (Rat, Rat),
    norm: Rat,
}

impl EpochFresh {
    pub(crate) fn certificate_face(
        &self,
        phase_covector_scale: &EpochSeries,
    ) -> Result<EpochCertificateFace, HnnError> {
        if (phase_covector_scale.rows, phase_covector_scale.columns) != (1, 1)
            || phase_covector_scale.numerators.len() != 1
            || !phase_covector_scale.denominator.is_positive()
            || phase_covector_scale.numerators[0].is_negative()
        {
            return Err(refused(
                "the epoch certificate needs phase three's nonnegative covector scale",
            ));
        }
        let (numerators, denominator) = self.direction.integral_chart()?;
        let unit = IntegralMatrix::from_grouped(
            self.direction.rows,
            self.direction.columns,
            numerators,
            denominator,
        )?;
        let scalar = |value: &EpochArray| {
            Rat::new(
                value.values[0].clone(),
                BigInt::from(value.row_divisors[0]) << value.exponent as usize,
            )
        };
        let unit_norms = unit.schur_norms();
        Ok(EpochCertificateFace {
            unit,
            alignment: scalar(&self.alignment),
            moves: scalar(&self.moves),
            covector: Rat::new(
                phase_covector_scale.numerators[0].clone(),
                phase_covector_scale.denominator.clone(),
            ),
            unit_norms,
            norm: EpochSpectral::grouped_frobenius(&self.direction),
        })
    }
}

impl EpochCertificateFace {
    fn direction(&self) -> PreparedDirectionRef<'_> {
        PreparedDirectionRef {
            unit: &self.unit,
            alignment: &self.alignment,
            moves: &self.moves,
            covector: &self.covector,
            unit_norms: &self.unit_norms,
            epoch_norm: Some(&self.norm),
        }
    }
}

impl Constitution {
    /// The epoch joins every locus to the existing tightened certificate. The
    /// nonlinear families, when present, participate in the same joint triangle.
    /// `readout` is the producing receiving map's maintained spectral cache.
    #[cfg(test)]
    pub(super) fn certify_epoch_gains(
        &self,
        reach: &Reach,
        linear: &[(LinearLocus, EpochCertificateFace)],
        factors: &[(Locus, &FactorPrepared)],
        loaded: Option<&crate::hnn::word::finite_gain::FiniteContactSpans>,
        readout: &EpochSpectral,
    ) -> Result<CertifiedSteps, HnnError> {
        let directions: Vec<_> = linear
            .iter()
            .map(|(kind, face)| (kind.locus(), *kind, face.direction()))
            .collect();
        let bound = readout.upper();
        self.certify_steps(
            Some(reach),
            &directions,
            factors,
            loaded,
            StepSource::Certified,
            Some(&bound),
            None,
        )?
        .map_err(|_| refused("the native epoch certificate returned a candidate refusal"))
    }
}

impl EpochLaw {
    pub(crate) fn declared_symmetry(&self) -> Option<&PortSymmetry> {
        self.symmetry.as_ref()
    }

    pub(crate) fn validate_against_native(
        &self,
        declaration: &NormalLaw,
        receiver_grain: u32,
        source_refinement: bool,
    ) -> Result<(), HnnError> {
        if self.source_refinement && !source_refinement {
            return Err(refused(
                "an epoch source refinement must match its native locus",
            ));
        }
        if (self.map.rows, self.map.columns)
            != (declaration.map().rows(), declaration.map().columns())
            || self.receiver_grain != receiver_grain
            || self.symmetry.as_ref() != declaration.symmetry()
        {
            return Err(refused(
                "an epoch checkpoint must match the native port shape, receiver grain, and paired declaration",
            ));
        }
        let mut founded = Self::from_normal(declaration, receiver_grain)?;
        founded.source_refinement = self.source_refinement;
        if declaration.receiving_prior().is_some() {
            // `continued` has the actual native law but not its field period.
            // Only that declared receiving role may defer the row binding;
            // `admit_epoch_field` binds it before a resident can be mounted.
            checkpoint::validate_receiving_before_field(self, &founded)
        } else {
            checkpoint::validate(self, &founded)
        }
    }

    pub(crate) fn founded(
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        prior_scale: u32,
    ) -> Result<Self, HnnError> {
        if rows == 0 || columns == 0 {
            return Err(refused("an epoch normal locus needs both ports"));
        }
        let mut gram = EpochArray::zero(columns, columns)?;
        for j in 0..columns {
            gram.values[j * columns + j] = BigInt::one() << prior_scale as usize;
        }
        gram.numerator_l1_bound = gram.values.iter().map(Signed::abs).sum();
        let width = u64::try_from(columns).map_err(|_| extent())?;
        Ok(Self {
            map: EpochArray::zero(rows, columns)?,
            gram,
            news: EpochArray::zero(rows, columns)?,
            receiver_grain,
            map_lattice: receiver_grain
                .checked_add(ceil_log2_count(width))
                .ok_or_else(extent)?,
            source_refinement: false,
            crossings: 0,
            spectral: EpochSpectral::founded_zero(rows, columns),
            symmetry: None,
        })
    }

    /// Import complete grouped state. The caller supplies the native row
    /// declaration, including the receiving phase period, as part of `news`.
    /// Validation is identical to cold restore and checks the exact metric,
    /// lattice and paired family before publication.
    pub(crate) fn from_grouped(
        map: EpochArray,
        gram: EpochArray,
        news: EpochArray,
        receiver_grain: u32,
        crossings: u64,
        symmetry: Option<PortSymmetry>,
    ) -> Result<Self, HnnError> {
        map.admit_grouped()?;
        gram.admit_grouped()?;
        news.admit_grouped()?;
        let columns = u64::try_from(map.columns).map_err(|_| extent())?;
        let mut spectral = EpochSpectral::founded_zero(map.rows, map.columns);
        spectral.refresh(&map)?;
        let candidate = Self {
            map,
            gram,
            news,
            receiver_grain,
            map_lattice: receiver_grain
                .checked_add(ceil_log2_count(columns))
                .ok_or_else(extent)?,
            source_refinement: false,
            crossings,
            spectral,
            symmetry,
        };
        checkpoint::validate(&candidate, &candidate)?;
        Ok(candidate)
    }

    /// An explicit transition from the old normal law. Nonzero legacy error
    /// feedback has a different meaning from R=B-WH and cannot be silently lost
    /// or relabelled as epoch news. The caller must resolve that transition.
    pub(crate) fn from_normal(law: &NormalLaw, receiver_grain: u32) -> Result<Self, HnnError> {
        if law.epoch_law().is_some() || !law.chart.support.is_empty() {
            return Err(refused(
                "only the native founding declaration imports into an epoch law",
            ));
        }
        if law.map_remainder().entries().iter().any(|v| !v.is_zero())
            || law.gram_remainder().entries().iter().any(|v| !v.is_zero())
        {
            return Err(refused(
                "transition to an epoch law must account for nonzero legacy map and Gram carry",
            ));
        }
        let map = EpochArray::from_dyadic_matrix(law.map())?;
        let gram = EpochArray::from_dyadic_matrix(&law.gram())?;
        let news = EpochArray::zero(map.rows, map.columns)?;
        Self::from_grouped(map, gram, news, receiver_grain, 0, law.symmetry.clone())
    }

    pub(crate) fn founded_paired(
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        prior_scale: u32,
        symmetry: PortSymmetry,
    ) -> Result<Self, HnnError> {
        if symmetry.rows().len() != rows || symmetry.columns().len() != columns {
            return Err(refused(
                "a founded epoch's paired family must match its ports",
            ));
        }
        Ok(Self {
            symmetry: Some(symmetry),
            ..Self::founded(rows, columns, receiver_grain, prior_scale)?
        })
    }

    /// Declare receiving phase rows from the field's own period before the
    /// first crossing. W and H remain dyadic; only carried R has odd row factors.
    pub(crate) fn with_phase_rows(
        mut self,
        phase_rows: &[usize],
        period: u64,
    ) -> Result<Self, HnnError> {
        if self.crossings != 0 || !self.news.is_zero() || period <= 1 || period % 2 == 0 {
            return Err(refused(
                "receiving phase rows need their odd field period at founding",
            ));
        }
        let mut seen = vec![false; self.news.rows];
        for &row in phase_rows {
            if row >= seen.len() || seen[row] {
                return Err(refused("receiving phase rows are distinct declared rows"));
            }
            seen[row] = true;
            self.news.row_divisors[row] = period;
        }
        if let Some(symmetry) = &self.symmetry {
            if (0..seen.len()).any(|row| seen[row] != seen[symmetry.rows()[row]]) {
                return Err(refused(
                    "paired receiving phase rows must be closed under row symmetry",
                ));
            }
        }
        Ok(self)
    }

    fn admit_flow(&self, flow: &EpochFlow) -> Result<(), HnnError> {
        let expected = partition_exponent(flow.receiver_grain, flow.partition_cells, flow.epoch)?;
        if flow.cells > flow.partition_cells
            || flow.partition_exponent != expected
            || flow.partitions.iter().any(|part| {
                part.unit_exponent != expected
                    || !part.denominator.is_positive()
                    || part
                        .remainder_numerators
                        .iter()
                        .any(|r| r.abs() >= part.denominator)
            })
        {
            return Err(refused(
                "an epoch flow must preserve its actual face bound, ingress c, partition exponent, and exact release bound",
            ));
        }
        if !self.map.is_dyadic() || !self.gram.is_dyadic() || !flow.gram.is_dyadic() {
            return Err(refused("the epoch map and Gram must remain dyadic"));
        }
        self.news.same_shape(&flow.covector)?;
        if self
            .news
            .row_divisors
            .iter()
            .zip(&flow.covector.row_divisors)
            .any(|(&a, &b)| b != 1 && a != b)
        {
            return Err(refused(
                "fresh epoch news must meet its declared receiving phase rows",
            ));
        }
        Ok(())
    }

    fn direction(
        &self,
        news: &EpochArray,
        gram: &EpochArray,
        support: &[usize],
    ) -> Result<(EpochArray, Vec<i64>), HnnError> {
        let columns = self.map.columns;
        let mut shares = vec![0i64; columns];
        let mut reached = vec![false; columns];
        for &j in support {
            if j >= columns {
                return Err(refused("an epoch direction names its reached support only"));
            }
            reached[j] = true;
            let mass: BigInt = (0..columns)
                .map(|i| gram.values[i * columns + j].abs())
                .sum();
            if mass.is_zero() {
                return Err(refused("a reached junction needs positive conductance"));
            }
            let bits = mass.bits() - u64::from((&mass & (&mass - BigInt::one())).is_zero());
            shares[j] = i64::try_from(bits).map_err(|_| extent())? - i64::from(gram.exponent);
        }
        let exponent =
            i64::from(news.exponent) + support.iter().map(|&j| shares[j]).max().unwrap_or(0);
        let exponent = u32::try_from(exponent.max(0)).map_err(|_| extent())?;
        let values = news
            .values
            .iter()
            .enumerate()
            .map(|(i, v)| {
                let j = i % columns;
                if reached[j] {
                    v << (i64::from(exponent) - i64::from(news.exponent) - shares[j]) as usize
                } else {
                    BigInt::zero()
                }
            })
            .collect();
        Ok((
            EpochArray::with_row_divisors(
                news.rows,
                columns,
                exponent,
                values,
                news.row_divisors.clone(),
            )?,
            shares,
        ))
    }

    /// [derived component; #62] Minimum weighted norm on the reached segment from a to b.
    /// S is read by the existing direction owner; its full column sums, support and row
    /// divisors remain operative. This theorem does not authorize a projected material move.
    fn joint_direction(
        &self,
        a: &EpochArray,
        b: &EpochArray,
        gram: &EpochArray,
        support: &[usize],
        locus: LinearLocus,
        source_budget: Option<(u64, u64, Locus)>,
    ) -> Result<EpochProposedDirection, HnnError> {
        let c = b.subtract(a)?;
        let (scaled_c, shares) = self.direction(&c, gram, support)?;
        let q = c.dot(&scaled_c)?.scalar_ratio()?;
        let n = b.dot(&scaled_c)?.scalar_ratio()?;
        if q.is_negative() {
            return Err(refused(
                "the joint segment needs its positive reached normal metric",
            ));
        }
        let alpha = if q.is_zero() {
            Rat::one()
        } else {
            (&n / &q).max(Rat::zero()).min(Rat::one())
        };
        let (k, t) = (alpha.numer().clone(), alpha.denom().clone());
        if let Some((budget, commit, at)) = source_budget {
            // Bound the transient scaled numerators and common divisor BEFORE their per-entry
            // multiplication/shifts. This is the original whole budget, never a new allowance.
            let exponent = a.exponent.max(b.exponent);
            let bits = |array: &EpochArray| {
                array
                    .values
                    .iter()
                    .map(BigInt::bits)
                    .max()
                    .unwrap_or(0)
                    .saturating_add(u64::from(exponent - array.exponent))
            };
            let width = u64::try_from(a.values.len()).map_err(|_| extent())?;
            let predicted = width
                .saturating_mul(
                    bits(a)
                        .max(bits(b))
                        .saturating_add(t.bits())
                        .saturating_add(2),
                )
                .saturating_add(t.bits())
                .saturating_add(u64::from(exponent));
            if predicted > budget {
                return Err(HnnError::ConstitutionBudget {
                    bits: predicted,
                    budget,
                    commit,
                    loci: vec![at],
                });
            }
        }
        let integer = |value| EpochArray::from_dyadic_scalar(&Rat::from_integer(value));
        let weighted = a
            .scalar_product(&integer(k.clone())?)?
            .add(&b.scalar_product(&integer(&t - &k)?)?)?;
        // w is the reached segment, not old unreached news. No default share is divided.
        let mut reached = vec![false; weighted.columns];
        for &column in support {
            reached[column] = true;
        }
        let numerator_w = EpochArray::with_row_divisors(
            weighted.rows,
            weighted.columns,
            weighted.exponent,
            weighted
                .values
                .iter()
                .enumerate()
                .map(|(at, value)| {
                    if reached[at % weighted.columns] {
                        value.clone()
                    } else {
                        BigInt::zero()
                    }
                })
                .collect(),
            weighted.row_divisors.clone(),
        )?;
        let (direction, _) = self.direction(&numerator_w, gram, support)?;
        let divisor = Rat::from_integer(t.clone());
        let normal_pairing = a.dot(&direction)?.scalar_ratio()? / &divisor;
        let current_scaled_pairing = b.dot(&direction)?.scalar_ratio()? / &divisor;
        let squared_norm = numerator_w.dot(&direction)?.scalar_ratio()? / (&divisor * &divisor);
        let reading = EpochJointDirectionReading {
            locus,
            alpha,
            metric_n: n,
            metric_q: q,
            support: support.to_vec(),
            shares: shares.clone(),
            numerator_w: EpochSeriesReading::of(&numerator_w),
            numerator_direction: EpochSeriesReading::of(&direction),
            divisor: t.clone(),
            normal_pairing,
            current_scaled_pairing,
            squared_norm,
            zero_direction: direction.is_zero(),
            projected_step: None,
            lattice_exponent: None,
            normal_fall: None,
            unit_lower_bound: None,
        };
        Ok(EpochProposedDirection {
            numerator: direction,
            divisor: t,
            shares,
            joint: Some(reading),
        })
    }

    /// Smallest L with 2^L max|numerator|/(2^exponent*divisor) >= 1.
    /// The one comparison shifts only to the already present operand's bit width.
    fn direction_reach(exponent: u32, maximum: &BigInt, divisor: &BigInt) -> Result<u32, HnnError> {
        if !maximum.is_positive() || !divisor.is_positive() {
            return Err(refused(
                "source reach requires positive actual direction magnitude and divisor",
            ));
        }
        let difference = i64::try_from(divisor.bits())
            .map_err(|_| extent())?
            .checked_sub(i64::try_from(maximum.bits()).map_err(|_| extent())?)
            .ok_or_else(extent)?;
        let above = if difference >= 0 {
            divisor > &(maximum << usize::try_from(difference).map_err(|_| extent())?)
        } else {
            (divisor << usize::try_from(-difference).map_err(|_| extent())?) > *maximum
        };
        let reach = i64::from(exponent)
            .checked_add(difference)
            .and_then(|value| value.checked_add(if above { 1 } else { 0 }))
            .ok_or_else(extent)?;
        u32::try_from(reach.max(0)).map_err(|_| extent())
    }

    pub(crate) fn fresh(&self, flow: &EpochFlow) -> Result<EpochFresh, HnnError> {
        if flow.receiver_grain != self.receiver_grain {
            return Err(refused(
                "fresh epoch news must use its life's receiver partition",
            ));
        }
        self.admit_flow(flow)?;
        let paired = self.symmetry.as_ref().map(|s| flow.paired(s)).transpose()?;
        let flow = paired.as_ref().unwrap_or(flow);
        self.gram.same_shape(&flow.gram)?;
        self.map.same_shape(&flow.covector)?;
        let gram = self.gram.add(&flow.gram)?;
        let (direction, shares) = self.direction(&flow.covector, &gram, &flow.support)?;
        let alignment = direction.dot(&flow.covector)?;
        let moves = direction.multiply(&flow.gram)?.dot(&direction)?;
        if alignment.values[0].is_negative() || moves.values[0].is_negative() {
            return Err(refused(
                "the epoch fresh direction violates its positive metric",
            ));
        }
        Ok(EpochFresh {
            direction,
            alignment,
            moves,
            shares,
        })
    }

    /// Absorb the certified fresh news at the solve's own unit step. The caller
    /// produces gamma from the fresh direction before this operation reads R.
    /// A nonzero step's exact fall is a typed invariant, never a step search.
    pub(crate) fn deposit(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
    ) -> Result<EpochDeposit, HnnError> {
        if (gamma.rows, gamma.columns) != (1, 1)
            || !gamma.is_dyadic()
            || gamma.values.iter().any(Signed::is_negative)
        {
            return Err(refused(
                "the epoch's certified fresh-news gain is nonnegative",
            ));
        }
        self.deposited_at(flow, gamma, BigInt::one(), BigInt::one())
    }

    /// Prepare source material at its active lattice. Publication additionally
    /// requires the actual represented-ray check in the epoch consumer. The
    /// budget is the whole native budget, an upper bound on this local payload.
    pub(crate) fn deposit_source(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        active_lattice: u32,
        budget: u64,
        commit: u64,
        ring: usize,
    ) -> Result<EpochDeposit, HnnError> {
        self.deposit_source_at_eta(
            flow,
            gamma,
            active_lattice,
            budget,
            commit,
            ring,
            BigInt::one(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn deposit_source_at_eta(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        active_lattice: u32,
        budget: u64,
        commit: u64,
        ring: usize,
        eta_numerator: BigInt,
    ) -> Result<EpochDeposit, HnnError> {
        self.deposit_source_proposal(
            flow,
            gamma,
            active_lattice,
            budget,
            commit,
            ring,
            eta_numerator,
            false,
            None,
        )
    }

    /// Joint is upstream-only and current-batch transient. The source checks and projection
    /// tail remain the original owner; a general segment divisor is never an eta denominator.
    fn deposit_joint(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        locus: LinearLocus,
        source: Option<(u32, u64, u64, usize)>,
        evidence: &mut Option<EpochStageRefusal>,
    ) -> Result<EpochDeposit, HnnError> {
        match locus {
            LinearLocus::SourcePort(ring) => {
                let (active, budget, commit, actual_ring) = source.ok_or_else(|| {
                    refused("a joint source proposal needs its actual source lattice and budget")
                })?;
                if ring != actual_ring {
                    return Err(refused("a joint source proposal keeps its source locus"));
                }
                self.deposit_source_proposal(
                    flow,
                    gamma,
                    active,
                    budget,
                    commit,
                    ring,
                    BigInt::one(),
                    true,
                    Some(evidence),
                )
            }
            LinearLocus::Contrast(_) => {
                if (gamma.rows, gamma.columns) != (1, 1)
                    || !gamma.is_dyadic()
                    || gamma.values.iter().any(Signed::is_negative)
                {
                    return Err(refused(
                        "the epoch's certified fresh-news gain is nonnegative",
                    ));
                }
                self.deposited_with_proposal(
                    flow,
                    gamma,
                    BigInt::one(),
                    BigInt::one(),
                    None,
                    Some(locus),
                    Some(evidence),
                )
            }
            LinearLocus::Receiving(_) => Err(refused(
                "the joint segment proposal is upstream only; receiving keeps its native certificate",
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn deposit_source_proposal(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        active_lattice: u32,
        budget: u64,
        commit: u64,
        ring: usize,
        eta_numerator: BigInt,
        joint: bool,
        evidence: Option<&mut Option<EpochStageRefusal>>,
    ) -> Result<EpochDeposit, HnnError> {
        if !self.news.is_dyadic() || !self.map.is_dyadic() {
            return Err(refused(
                "source refinement requires dyadic material and news",
            ));
        }
        if self.source_refinement && self.map_lattice != active_lattice {
            return Err(refused(
                "source epoch and active material lattices must agree",
            ));
        }
        if (gamma.rows, gamma.columns) != (1, 1)
            || !gamma.is_dyadic()
            || gamma.values.iter().any(Signed::is_negative)
        {
            return Err(refused(
                "the source fresh-news gain is nonnegative and dyadic",
            ));
        }
        let mut source = self.clone();
        source.source_refinement = true;
        source.map_lattice = source.map_lattice.max(active_lattice);
        let mut deposit = source.deposited_with_proposal(
            flow,
            gamma,
            eta_numerator,
            BigInt::one(),
            Some((budget, commit, Locus::SourcePort(ring))),
            joint.then_some(LinearLocus::SourcePort(ring)),
            evidence,
        )?;
        if deposit.step.is_zero() {
            // Representation is refined only with an actual admitted move.
            // A first zero crossing may still absorb F/G on the founded policy.
            deposit.successor.source_refinement = self.source_refinement;
            deposit.successor.map_lattice = self.map_lattice;
        }
        Ok(deposit)
    }

    fn deposited_at(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        eta_denominator: BigInt,
    ) -> Result<EpochDeposit, HnnError> {
        self.deposited_with_projection(flow, gamma, eta_numerator, eta_denominator, None)
    }

    fn deposited_with_projection(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        eta_denominator: BigInt,
        source_budget: Option<(u64, u64, Locus)>,
    ) -> Result<EpochDeposit, HnnError> {
        self.deposited_with_proposal(
            flow,
            gamma,
            eta_numerator,
            eta_denominator,
            source_budget,
            None,
            None,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn deposited_with_proposal(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        eta_denominator: BigInt,
        source_budget: Option<(u64, u64, Locus)>,
        joint_locus: Option<LinearLocus>,
        evidence: Option<&mut Option<EpochStageRefusal>>,
    ) -> Result<EpochDeposit, HnnError> {
        self.deposited_with_quantum_proposal(
            flow,
            gamma,
            eta_numerator,
            eta_denominator,
            source_budget,
            joint_locus,
            evidence,
            None,
        )
    }

    fn deposit_quantum(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        projection: &QuantumProjection,
    ) -> Result<EpochDeposit, HnnError> {
        if (gamma.rows, gamma.columns) != (1, 1)
            || !gamma.is_dyadic()
            || gamma.values.iter().any(Signed::is_negative)
        {
            return Err(refused(
                "the epoch's certified fresh-news gain is nonnegative",
            ));
        }
        self.deposited_with_quantum_proposal(
            flow,
            gamma,
            BigInt::one(),
            BigInt::one(),
            None,
            None,
            None,
            Some(projection),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn deposited_with_quantum_proposal(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        eta_denominator: BigInt,
        source_budget: Option<(u64, u64, Locus)>,
        joint_locus: Option<LinearLocus>,
        mut evidence: Option<&mut Option<EpochStageRefusal>>,
        quantum: Option<&QuantumProjection>,
    ) -> Result<EpochDeposit, HnnError> {
        if quantum.is_some()
            && (eta_numerator != BigInt::one()
                || eta_denominator != BigInt::one()
                || source_budget.is_some()
                || joint_locus.is_some()
                || !gamma.scalar_ratio()?.is_positive())
        {
            return Err(refused(
                "a quantum alternative needs a positive certified gain at unit receiving eta",
            ));
        }
        if eta_numerator.is_negative() || !eta_denominator.is_positive() {
            return Err(refused(
                "an epoch certificate needs a nonnegative step ratio",
            ));
        }
        if flow.receiver_grain != self.receiver_grain {
            return Err(refused(
                "an epoch flow must use its life's receiver partition",
            ));
        }
        self.admit_flow(flow)?;
        let paired = self.symmetry.as_ref().map(|s| flow.paired(s)).transpose()?;
        let flow = paired.as_ref().unwrap_or(flow);
        self.gram.same_shape(&flow.gram)?;
        self.map.same_shape(&flow.covector)?;
        let gram = self.gram.add(&flow.gram)?;
        let fresh = flow.covector.scalar_product(gamma)?;
        let news = self.news.add(&fresh)?;
        let proposed = if let Some(locus) = joint_locus {
            self.joint_direction(&news, &fresh, &gram, &flow.support, locus, source_budget)?
        } else {
            let (direction, shares) = self.direction(&news, &gram, &flow.support)?;
            EpochProposedDirection {
                numerator: direction,
                divisor: BigInt::one(),
                shares,
                joint: None,
            }
        };
        let EpochProposedDirection {
            numerator: direction,
            divisor: direction_divisor,
            shares,
            mut joint,
        } = proposed;
        let mut map_lattice = self.map_lattice;
        // A zero fresh gain or explicit zero material move certifies no new source motion.
        // Do not refine a lattice for a held map; H/R still absorb their actual operands.
        let source_held = source_budget.is_some() && (gamma.is_zero() || eta_numerator.is_zero());
        if source_budget.is_some() && !source_held && !direction.is_zero() {
            let maximum = direction
                .values
                .iter()
                .map(Signed::abs)
                .max()
                .expect("a nonzero source direction has a coordinate");
            // Source rows are dyadic: D = n / 2^e. The smallest l with
            // 2^l max|D| >= 1 is max(0, e-floor(log2(max|n|))).
            let whole = maximum.bits().checked_sub(1).ok_or_else(extent)?;
            let reach = if direction_divisor == BigInt::one() {
                u32::try_from(u64::from(direction.exponent).saturating_sub(whole))
                    .map_err(|_| extent())?
            } else {
                Self::direction_reach(direction.exponent, &maximum, &direction_divisor)?
            };
            map_lattice = map_lattice.max(reach);
        }
        if let Some((budget, commit, locus)) = source_budget {
            // Admit the allocation's actual upper extent before any shift to a
            // finer lattice. This is conservative, never an enlarged budget.
            let entries = u64::try_from(self.map.values.len()).map_err(|_| extent())?;
            let old_bits = self
                .map
                .values
                .iter()
                .map(BigInt::bits)
                .max()
                .unwrap_or(0)
                .saturating_add(u64::from(map_lattice.saturating_sub(self.map.exponent)));
            let move_bits = direction
                .values
                .iter()
                .map(BigInt::bits)
                .max()
                .unwrap_or(0)
                .saturating_add(u64::from(map_lattice.saturating_sub(direction.exponent)));
            let mut predicted = entries
                .saturating_mul(old_bits.max(move_bits).saturating_add(2))
                .saturating_add(u64::from(map_lattice));
            if joint.is_some() {
                predicted = predicted.saturating_add(direction_divisor.bits());
            }
            if predicted > budget {
                return Err(HnnError::ConstitutionBudget {
                    bits: predicted,
                    budget,
                    commit,
                    loci: vec![locus],
                });
            }
        }
        let shift = i64::from(map_lattice) - i64::from(direction.exponent);
        let projection_divisor = &eta_denominator * &direction_divisor;
        let denominator = if shift < 0 {
            &projection_divisor << (-shift) as usize
        } else {
            projection_divisor
        };
        let values = direction
            .values
            .iter()
            .enumerate()
            .map(|(index, v)| {
                if source_held {
                    return BigInt::zero();
                }
                let numerator = v * &eta_numerator;
                let numerator = if shift > 0 {
                    numerator << shift as usize
                } else {
                    numerator
                };
                numerator / (&denominator * direction.row_divisors[index / direction.columns])
            })
            .collect();
        let canonical = EpochArray::new(self.map.rows, self.map.columns, map_lattice, values)?;
        let step = match quantum {
            Some(projection) => projection.represent(self, flow, &news, &canonical)?,
            None => canonical,
        };
        let linear = step.dot(&news)?;
        let quadratic = step.multiply(&gram)?.dot(&step)?.half()?;
        let fall = linear.subtract(&quadratic)?;
        if let Some(reading) = &mut joint {
            reading.projected_step = Some(EpochSeriesReading::of(&step));
            reading.lattice_exponent = Some(map_lattice);
            reading.normal_fall = Some(fall.scalar_ratio()?);
        }
        if !step.is_zero() && !fall.values[0].is_positive() {
            if let (Some(reading), Some(target)) = (&joint, evidence.as_deref_mut()) {
                EpochStageRefusal::at(
                    "joint_normal_projection",
                    EpochStageCondition::JointNormalFall,
                    "nonzero represented P requires retained normal fall > 0",
                    Some(reading.locus.locus()),
                    Some(Family::Map),
                )
                .read(
                    "joint_direction",
                    EpochStageValue::JointDirection(reading.clone()),
                )
                .read(
                    "normal_linear",
                    EpochStageValue::Ratio(linear.scalar_ratio()?),
                )
                .read(
                    "normal_quadratic",
                    EpochStageValue::Ratio(quadratic.scalar_ratio()?),
                )
                .read(
                    "unit_lower_bound",
                    EpochStageValue::Unavailable(
                        "not read: the earlier normal positivity guard failed",
                    ),
                )
                .first(target);
            }
            return Err(HnnError::EpochStepNonDescending {
                crossing: self.crossings,
            });
        }
        if eta_numerator == BigInt::one() && eta_denominator == BigInt::one() {
            let mut lower = Rat::zero();
            for (index, value) in step.values.iter().enumerate() {
                let share = shares[index % step.columns];
                let exponent = share - 2 * i64::from(step.exponent) - 1;
                let square = value * value;
                lower += if exponent >= 0 {
                    Rat::from_integer(square << exponent as usize)
                } else {
                    Rat::new(square, BigInt::one() << (-exponent) as usize)
                };
            }
            if let Some(reading) = &mut joint {
                reading.unit_lower_bound = Some(lower.clone());
            }
            if fall.scalar_ratio()? < lower {
                if let (Some(reading), Some(target)) = (&joint, evidence.as_deref_mut()) {
                    EpochStageRefusal::at("joint_normal_projection", EpochStageCondition::JointNormalFall,
                        "at unit eta the retained normal fall >= half the S-weighted represented squared move", Some(reading.locus.locus()), Some(Family::Map))
                        .read("joint_direction", EpochStageValue::JointDirection(reading.clone()))
                        .read("normal_linear", EpochStageValue::Ratio(linear.scalar_ratio()?))
                        .read("normal_quadratic", EpochStageValue::Ratio(quadratic.scalar_ratio()?))
                        .read("unit_lower_bound", EpochStageValue::Ratio(lower.clone())).first(target);
                }
                return Err(HnnError::EpochStepNonDescending {
                    crossing: self.crossings,
                });
            }
        }
        let map = self.map.add(&step)?;
        let news = news.subtract(&step.multiply(&gram)?)?;
        let mut spectral = self.spectral.clone();
        spectral.observe_move(&step)?;
        // The carried remainder is retained exactly; even an inaudible step
        // leaves its certified target in R rather than rounding it away.
        let expected = self
            .map
            .multiply(&gram)?
            .add(&self.news)?
            .add(&flow.covector.scalar_product(gamma)?)?;
        if map.multiply(&gram)?.add(&news)? != expected {
            return Err(refused(
                "the epoch deposit must preserve W_new H_new + R_new = W_old H_new + gamma G + R_old",
            ));
        }
        if let Some(symmetry) = &self.symmetry {
            for row in 0..map.rows {
                for column in 0..map.columns {
                    if let Some(partner) = symmetry.columns()[column] {
                        let own = row * map.columns + column;
                        let paired = symmetry.rows()[row] * map.columns + partner;
                        if map.values[own] != map.values[paired]
                            || news.values[own] != news.values[paired]
                            || news.row_divisors[row] != news.row_divisors[symmetry.rows()[row]]
                        {
                            return Err(refused(
                                "the epoch map and carried news must preserve paired symmetry",
                            ));
                        }
                    }
                }
            }
            for row in 0..gram.rows {
                for column in 0..gram.columns {
                    if gram.values[row * gram.columns + column]
                        != gram.values
                            [symmetry.column(row) * gram.columns + symmetry.column(column)]
                    {
                        return Err(refused("the epoch Gram must preserve paired symmetry"));
                    }
                }
            }
        }
        let successor = Self {
            map,
            gram,
            news,
            spectral,
            map_lattice,
            crossings: self.crossings.checked_add(1).ok_or_else(extent)?,
            ..self.clone()
        };
        Ok(EpochDeposit {
            quantum_projection: quantum.cloned(),
            successor,
            step,
            fall,
            eta_numerator,
            eta_denominator,
            halvings: 0,
            direction,
            direction_divisor,
            joint_direction: joint,
            shares,
        })
    }

    /// Called by the continuing consumer at the actual field aeon's close.
    pub(crate) fn refresh_spectral(&mut self) -> Result<(), HnnError> {
        self.spectral.refresh(&self.map)
    }

    /// Earlier controls exercise identities at arbitrary represented steps. This
    /// search exists only in tests; production fixes eta=1 and refuses a defect.
    #[cfg(test)]
    fn identity_step(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        mut eta_denominator: BigInt,
    ) -> Result<EpochDeposit, HnnError> {
        let mut halvings = 0u64;
        loop {
            match self.deposited_at(flow, gamma, eta_numerator.clone(), eta_denominator.clone()) {
                Ok(mut deposit) => {
                    deposit.halvings = halvings;
                    return Ok(deposit);
                }
                Err(HnnError::EpochStepNonDescending { .. }) => {
                    eta_denominator <<= 1usize;
                    halvings = halvings.checked_add(1).ok_or_else(extent)?;
                }
                Err(error) => return Err(error),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;

    fn array(rows: usize, columns: usize, exponent: u32, values: &[i64]) -> EpochArray {
        EpochArray::new(
            rows,
            columns,
            exponent,
            values.iter().copied().map(BigInt::from).collect(),
        )
        .unwrap()
    }

    fn scalar(value: i64) -> EpochArray {
        array(1, 1, 0, &[value])
    }

    fn series(rows: usize, columns: usize, numerators: &[i64], denominator: i64) -> EpochSeries {
        EpochSeries {
            rows,
            columns,
            numerators: numerators.iter().copied().map(BigInt::from).collect(),
            denominator: BigInt::from(denominator),
        }
    }

    fn values(array: &EpochArray) -> Vec<Vec<Rat>> {
        let denominator = BigInt::one() << array.exponent as usize;
        array
            .values
            .chunks(array.columns)
            .enumerate()
            .map(|(index, row)| {
                row.iter()
                    .map(|n| Rat::new(n.clone(), &denominator * array.row_divisors[index]))
                    .collect()
            })
            .collect()
    }

    fn product(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Vec<Vec<Rat>> {
        (0..a.len())
            .map(|i| {
                (0..b[0].len())
                    .map(|j| (0..b.len()).map(|k| &a[i][k] * &b[k][j]).sum())
                    .collect()
            })
            .collect()
    }

    fn objective(w: &[Vec<Rat>], h: &[Vec<Rat>], b: &[Vec<Rat>]) -> Rat {
        let mut quadratic = Rat::zero();
        let mut target = Rat::zero();
        for i in 0..w.len() {
            for j in 0..w[i].len() {
                target += &w[i][j] * &b[i][j];
                for k in 0..w[i].len() {
                    quadratic += &w[i][j] * &h[j][k] * &w[i][k];
                }
            }
        }
        quadratic / integer(2) - target
    }

    fn samples() -> Vec<EpochSample> {
        vec![
            EpochSample {
                feature: array(1, 2, 1, &[2, 1]),
                positive: array(2, 1, 0, &[1, 0]),
                foil: series(2, 1, &[2, 3], 5),
                metric_weight: series(1, 1, &[1], 3),
            },
            EpochSample {
                feature: array(1, 2, 1, &[1, 2]),
                positive: array(2, 1, 0, &[0, 1]),
                foil: series(2, 1, &[3, 2], 5),
                metric_weight: series(1, 1, &[1], 3),
            },
        ]
    }

    #[test]
    fn quotient_partition_and_any_length_bound_are_exact() {
        for epoch in [0, 1, 2, 3, 4, 7, 8, 704_776] {
            let l = partition_exponent(32, 231, epoch).unwrap();
            assert_eq!(l, 41 + 2 * ceil_log2_count(epoch + 1));
            for denominator in [
                BigInt::from(3),
                BigInt::from(29),
                (BigInt::one() << 130usize) + 7,
            ] {
                let input = EpochSeries {
                    rows: 2,
                    columns: 2,
                    numerators: vec![
                        BigInt::from(-17),
                        BigInt::zero(),
                        BigInt::one() << 190usize,
                        (BigInt::one() << 130usize) + 3,
                    ],
                    denominator: denominator.clone(),
                };
                let split = input.partition(l).unwrap();
                for k in 0..4 {
                    let q = &split.retained.values[k] << (l - split.retained.exponent) as usize;
                    assert_eq!(
                        &input.numerators[k] << l as usize,
                        &q * &denominator + &split.remainder_numerators[k]
                    );
                    assert!(split.remainder_numerators[k].abs() < denominator);
                    if !split.remainder_numerators[k].is_zero() {
                        assert_eq!(
                            split.remainder_numerators[k].sign(),
                            input.numerators[k].sign()
                        );
                    }
                }
            }
        }
        assert_eq!(partition_exponent(32, 231, 0).unwrap(), 41);
        assert_eq!(partition_exponent(32, 231, 704_776).unwrap(), 81);
        for k in [1, 2, 3, 231, 256, 257] {
            let bound = lifetime_release_bound(32, k).unwrap();
            let expected = Rat::new(
                BigInt::from(k) * 3,
                BigInt::one() << (34 + ceil_log2_count(k)) as usize,
            );
            assert_eq!(values(&bound)[0][0], expected);
            assert!(expected < Rat::new(BigInt::one(), BigInt::one() << 32usize));
        }
    }

    #[test]
    fn actual_step_preserves_news_energy_and_paired_symmetry() {
        let mut state = EpochLaw::founded(2, 2, 32, 0).unwrap();
        for epoch in 0..8 {
            let flow = EpochFlow::from_samples(2, 2, 32, 231, epoch, &samples()).unwrap();
            let result = state
                .identity_step(&flow, &scalar(1), BigInt::from(64), BigInt::one())
                .unwrap();
            let h = values(&result.successor.gram);
            let before = values(&state.map);
            let after = values(&result.successor.map);
            let old_news = values(&state.news);
            let new_news = values(&result.successor.news);
            let g = values(&flow.covector);
            let wh = product(&before, &h);
            let b: Vec<Vec<Rat>> = (0..2)
                .map(|i| {
                    (0..2)
                        .map(|j| &wh[i][j] + &old_news[i][j] + &g[i][j])
                        .collect()
                })
                .collect();
            let successor_wh = product(&after, &h);
            for i in 0..2 {
                for j in 0..2 {
                    assert_eq!(&successor_wh[i][j] + &new_news[i][j], b[i][j]);
                    assert_eq!(after[i][j], after[1 - i][1 - j]);
                    assert_eq!(h[i][j], h[1 - i][1 - j]);
                    assert_eq!(new_news[i][j], new_news[1 - i][1 - j]);
                }
            }
            let direct_fall = objective(&before, &h, &b) - objective(&after, &h, &b);
            assert_eq!(values(&result.fall)[0][0], direct_fall);
            if result.step.is_zero() {
                assert!(direct_fall.is_zero());
            } else {
                assert!(direct_fall.is_positive());
            }
            assert!(result.halvings > 0);
            for partition in &flow.partitions {
                assert!(
                    partition
                        .remainder_numerators
                        .iter()
                        .all(|r| r.abs() < partition.denominator)
                );
            }
            state = result.successor;
        }
        assert!(!state.map.is_zero());
        assert!(!state.news.is_zero());
    }

    #[test]
    fn explicit_pump_and_step_ratios_preserve_the_actual_news_balance() {
        for gamma in [scalar(0), scalar(1), array(1, 1, 3, &[3]), scalar(4)] {
            let mut state = EpochLaw::founded(2, 2, 32, 0).unwrap();
            for epoch in 0..4 {
                let flow = EpochFlow::from_samples(2, 2, 32, 231, epoch, &samples()).unwrap();
                let result = state
                    .identity_step(&flow, &gamma, BigInt::from(9), BigInt::from(7))
                    .unwrap();
                let h = values(&result.successor.gram);
                let before = values(&state.map);
                let after = values(&result.successor.map);
                let old_news = values(&state.news);
                let new_news = values(&result.successor.news);
                let g = values(&flow.covector);
                let pump = &values(&gamma)[0][0];
                let wh = product(&before, &h);
                let b: Vec<Vec<Rat>> = (0..2)
                    .map(|i| {
                        (0..2)
                            .map(|j| &wh[i][j] + &old_news[i][j] + pump * &g[i][j])
                            .collect()
                    })
                    .collect();
                let successor_wh = product(&after, &h);
                for i in 0..2 {
                    for j in 0..2 {
                        assert_eq!(&successor_wh[i][j] + &new_news[i][j], b[i][j]);
                    }
                }
                let fall = objective(&before, &h, &b) - objective(&after, &h, &b);
                assert_eq!(values(&result.fall)[0][0], fall);
                assert!(fall >= Rat::zero());
                if gamma.is_zero() {
                    assert!(result.step.is_zero());
                    assert!(result.successor.news.is_zero());
                }
                state = result.successor;
            }
        }
    }

    #[test]
    fn paired_epoch_projects_the_flow_and_rejects_outside_features() {
        let symmetry =
            PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0), None], &[0]).unwrap();
        let mut state = EpochLaw::founded_paired(2, 3, 32, 1, symmetry).unwrap();
        let mut total_metric = integer(2);
        for epoch in 0..6 {
            let feature = if epoch % 2 == 0 { [1, 0, 0] } else { [0, 1, 0] };
            let sample = EpochSample {
                feature: array(1, 3, 0, &feature),
                positive: array(2, 1, 0, &[1, 0]),
                foil: series(2, 1, &[1, 2], 3),
                metric_weight: series(1, 1, &[1], 3),
            };
            let flow = EpochFlow::from_samples(2, 3, 32, 231, epoch, &[sample]).unwrap();
            let g = values(&flow.covector);
            let own = if epoch % 2 == 0 { 0 } else { 1 };
            let other = 1 - own;
            // Independent explicit half-sum in this two-column family. No
            // projected-flow helper participates in this energy/news oracle.
            let mut projected_g = vec![vec![Rat::zero(); 3]; 2];
            projected_g[0][own] = &g[0][own] / integer(2);
            projected_g[1][other] = projected_g[0][own].clone();
            projected_g[1][own] = &g[1][own] / integer(2);
            projected_g[0][other] = projected_g[1][own].clone();
            total_metric += &values(&flow.gram)[own][own] / integer(2);
            let expected_h = vec![
                vec![total_metric.clone(), Rat::zero(), Rat::zero()],
                vec![Rat::zero(), total_metric.clone(), Rat::zero()],
                vec![Rat::zero(), Rat::zero(), integer(2)],
            ];
            let before = values(&state.map);
            let before_news = values(&state.news);
            let before_wh = product(&before, &expected_h);
            let b: Vec<Vec<Rat>> = (0..2)
                .map(|i| {
                    (0..3)
                        .map(|j| &before_wh[i][j] + &before_news[i][j] + &projected_g[i][j])
                        .collect()
                })
                .collect();
            let result = state
                .identity_step(&flow, &scalar(1), BigInt::from(64), BigInt::one())
                .unwrap();
            assert_eq!(values(&result.successor.gram), expected_h);
            assert_eq!(result.shares[0], result.shares[1]);
            let after = values(&result.successor.map);
            let news = values(&result.successor.news);
            let wh = product(&after, &expected_h);
            for i in 0..2 {
                for j in 0..3 {
                    assert_eq!(&wh[i][j] + &news[i][j], b[i][j]);
                }
                assert_eq!(after[i][0], after[1 - i][1]);
                assert_eq!(news[i][0], news[1 - i][1]);
                assert!(after[i][2].is_zero());
                assert!(news[i][2].is_zero());
            }
            assert_eq!(
                values(&result.fall)[0][0],
                objective(&before, &expected_h, &b) - objective(&after, &expected_h, &b)
            );
            state = result.successor;
        }
        let outside = EpochSample {
            feature: array(1, 3, 0, &[0, 0, 1]),
            positive: array(2, 1, 0, &[1, 0]),
            foil: series(2, 1, &[1, 2], 3),
            metric_weight: series(1, 1, &[1], 3),
        };
        let flow = EpochFlow::from_samples(2, 3, 32, 231, 6, &[outside]).unwrap();
        assert!(matches!(
            state.identity_step(&flow, &scalar(1), BigInt::one(), BigInt::one()),
            Err(HnnError::PairedOutside { class: 2 })
        ));
    }

    #[test]
    fn unit_solve_meets_the_exact_majorizer_fall_without_a_search() {
        let mut state = EpochLaw::founded(2, 2, 32, 0).unwrap();
        for epoch in 0..12 {
            let flow = EpochFlow::from_samples(2, 2, 32, 231, epoch, &samples()).unwrap();
            let gamma = match epoch % 4 {
                0 => scalar(0),
                1 => scalar(1),
                2 => array(1, 1, 3, &[3]),
                _ => scalar(4),
            };
            let result = state.deposit(&flow, &gamma).unwrap();
            assert_eq!(result.eta_numerator, BigInt::one());
            assert_eq!(result.eta_denominator, BigInt::one());
            assert_eq!(result.halvings, 0);
            let step = values(&result.step);
            let gram = values(&result.successor.gram);
            let old_map = values(&state.map);
            let old_news = values(&state.news);
            let g = values(&flow.covector);
            let pump = &values(&gamma)[0][0];
            let wh = product(&old_map, &gram);
            let b: Vec<Vec<Rat>> = (0..2)
                .map(|i| {
                    (0..2)
                        .map(|j| &wh[i][j] + &old_news[i][j] + pump * &g[i][j])
                        .collect()
                })
                .collect();
            let fall = objective(&old_map, &gram, &b)
                - objective(&values(&result.successor.map), &gram, &b);
            assert_eq!(values(&result.fall)[0][0], fall);
            let mut guaranteed = Rat::zero();
            for j in 0..2 {
                let share = result.shares[j];
                let conductance = if share >= 0 {
                    Rat::from_integer(BigInt::one() << share as usize)
                } else {
                    Rat::new(BigInt::one(), BigInt::one() << (-share) as usize)
                };
                for row in &step {
                    guaranteed += &conductance * &row[j] * &row[j] / integer(2);
                }
            }
            assert!(fall >= guaranteed);
            assert_eq!(result.step.is_zero(), fall.is_zero());
            let new_wh = product(&values(&result.successor.map), &gram);
            let new_news = values(&result.successor.news);
            for i in 0..2 {
                for j in 0..2 {
                    assert_eq!(&new_wh[i][j] + &new_news[i][j], b[i][j]);
                }
            }
            state = result.successor;
        }
    }

    #[test]
    fn a_broken_majorizer_is_a_typed_defect_without_publication() {
        let state = EpochLaw::founded(1, 2, 32, 0).unwrap();
        let before = state.clone();
        // An invalid internal flow: its Gram is asymmetric, so the symmetric
        // majorizer's hypothesis is false. The owner must report the fall defect,
        // never conceal it by changing the absorption step.
        let mut broken = EpochFlow::from_samples(1, 2, 32, 231, 0, &[]).unwrap();
        broken.gram = array(2, 2, 0, &[0, 100, 0, 0]);
        broken.covector = array(1, 2, 0, &[10, 128]);
        broken.support = vec![0, 1];
        assert!(matches!(
            state.deposit(&broken, &scalar(1)),
            Err(HnnError::EpochStepNonDescending { crossing: 0 })
        ));
        assert_eq!(state, before);
    }

    fn joint_values(direction: &EpochProposedDirection) -> Vec<Rat> {
        direction
            .numerator
            .to_rows()
            .into_iter()
            .flatten()
            .map(|value| value / Rat::from_integer(direction.divisor.clone()))
            .collect()
    }

    #[test]
    fn exact_joint_segment_endpoints_odd_denominators_support_and_row_metric() {
        let law = EpochLaw::founded(1, 2, 3, 0).unwrap();
        let identity = array(2, 2, 0, &[1, 0, 0, 1]);
        let read = |a: &EpochArray, b: &EpochArray, gram: &EpochArray, support: &[usize]| {
            law.joint_direction(a, b, gram, support, LinearLocus::SourcePort(0), None)
                .unwrap()
        };
        for (a, b, expected) in [
            (array(1, 2, 0, &[1, 0]), array(1, 2, 0, &[2, 1]), Rat::one()),
            (
                array(1, 2, 0, &[2, 1]),
                array(1, 2, 0, &[1, 0]),
                Rat::zero(),
            ),
            (array(1, 2, 0, &[1, 0]), array(1, 2, 0, &[1, 0]), Rat::one()),
            (array(1, 2, 0, &[0, 0]), array(1, 2, 0, &[0, 0]), Rat::one()),
        ] {
            let proposal = read(&a, &b, &identity, &[0, 1]);
            let reading = proposal.joint.as_ref().unwrap();
            assert_eq!(reading.alpha, expected);
            assert!(reading.normal_pairing >= reading.squared_norm);
            assert!(reading.current_scaled_pairing >= reading.squared_norm);
            if a == b {
                assert_eq!(reading.metric_q, Rat::zero());
            }
        }
        let proposal = read(
            &array(1, 2, 0, &[1, 0]),
            &array(1, 2, 0, &[0, 1]),
            &array(2, 2, 0, &[1, 0, 0, 4]),
            &[0, 1],
        );
        assert_eq!(
            proposal.joint.as_ref().unwrap().alpha,
            integer(1) / integer(5)
        );
        assert_eq!(
            joint_values(&proposal),
            vec![integer(1) / integer(5), integer(1) / integer(5)]
        );
        assert_eq!(
            proposal.joint.as_ref().unwrap().squared_norm,
            integer(1) / integer(5)
        );
        let empty = read(
            &array(1, 2, 0, &[5, 7]),
            &array(1, 2, 0, &[9, 3]),
            &identity,
            &[],
        );
        assert!(empty.numerator.is_zero());
        assert_eq!(empty.joint.as_ref().unwrap().alpha, Rat::one());
        let masked = read(
            &array(1, 2, 0, &[1, 99]),
            &array(1, 2, 0, &[1, -99]),
            &identity,
            &[0],
        );
        assert_eq!(masked.joint.as_ref().unwrap().alpha, Rat::one());
        assert_eq!(joint_values(&masked), vec![Rat::one(), Rat::zero()]);
        assert!(
            law.joint_direction(
                &array(1, 2, 0, &[1, 0]),
                &array(1, 2, 0, &[0, 1]),
                &array(2, 2, 0, &[0, 0, 0, 1]),
                &[0],
                LinearLocus::SourcePort(0),
                None
            )
            .is_err()
        );
        // Arithmetic law only: actual odd row factors enter both occurrences in the metric.
        let a = EpochArray::with_row_divisors(1, 2, 0, vec![1.into(), 0.into()], vec![3]).unwrap();
        let b = EpochArray::with_row_divisors(1, 2, 0, vec![0.into(), 1.into()], vec![3]).unwrap();
        let odd = read(&a, &b, &identity, &[0, 1]);
        assert_eq!(
            joint_values(&odd),
            vec![integer(1) / integer(6), integer(1) / integer(6)]
        );
        assert_eq!(
            odd.joint.as_ref().unwrap().squared_norm,
            integer(1) / integer(18)
        );
    }

    fn projection_joint_fixture(a: &[i64], b: &[i64]) -> (EpochLaw, EpochFlow, Vec<Sample>) {
        let mut law = EpochLaw::founded(1, 2, 3, 0).unwrap();
        law.news = array(1, 2, 5, &[a[0] - b[0], a[1] - b[1]]);
        let samples: Vec<_> = (0..2)
            .map(|column| Sample {
                weight: Rat::one(),
                feature: (0..2)
                    .map(|j| if column == j { Rat::one() } else { Rat::zero() })
                    .collect(),
                covector: vec![integer(b[column]) / integer(32)],
                masses: None,
            })
            .collect();
        let records: Vec<_> = samples
            .iter()
            .map(|sample| EpochRecord::from_sample(sample).unwrap())
            .collect();
        let flow = EpochFlow::from_records(1, 2, 3, 2, 0, 2, &records).unwrap();
        (law, flow, samples)
    }

    #[test]
    fn joint_projection_keeps_both_normal_guards_and_the_present_alignment_refusal() {
        let gain = scalar(1);
        for (a, b, alpha, fall, lower) in [
            (
                [31, -1],
                [-4, 6],
                integer(1) / integer(7),
                -integer(3) / integer(512),
                None,
            ),
            (
                [11, 3],
                [-4, 6],
                integer(1) / integer(3),
                integer(1) / integer(512),
                Some(integer(1) / integer(256)),
            ),
        ] {
            let (law, flow, _) = projection_joint_fixture(&a, &b);
            let before = law.clone();
            let mut evidence = None;
            assert!(matches!(
                law.deposit_joint(
                    &flow,
                    &gain,
                    LinearLocus::SourcePort(0),
                    Some((4, 1 << 20, 0, 0)),
                    &mut evidence
                ),
                Err(HnnError::EpochStepNonDescending { crossing: 0 })
            ));
            let evidence = evidence.unwrap();
            assert_eq!(evidence.condition, EpochStageCondition::JointNormalFall);
            let reading = evidence
                .readings
                .iter()
                .find_map(|r| {
                    if let EpochStageValue::JointDirection(v) = &r.value {
                        Some(v)
                    } else {
                        None
                    }
                })
                .unwrap();
            assert_eq!(reading.alpha, alpha);
            assert_eq!(reading.normal_fall, Some(fall));
            assert_eq!(reading.unit_lower_bound, lower);
            assert!(!evidence.seal_formed && !evidence.finite_probe_executed);
            assert_eq!(law, before);
        }
        let (law, flow, samples) = projection_joint_fixture(&[-4, 6], &[31, -1]);
        let proposal = law
            .deposit_joint(
                &flow,
                &gain,
                LinearLocus::SourcePort(0),
                Some((4, 1 << 20, 0, 0)),
                &mut None,
            )
            .unwrap();
        assert_eq!(proposal.eta_numerator, BigInt::one());
        assert_eq!(
            proposal.eta_denominator,
            BigInt::one(),
            "the segment divisor must never bypass the unit normal lower-bound guard"
        );
        assert_eq!(proposal.direction_divisor, BigInt::from(7));
        assert_eq!(
            proposal.fall.scalar_ratio().unwrap(),
            integer(1) / integer(128)
        );
        let reading = proposal.joint_direction.as_ref().unwrap();
        assert_eq!(reading.alpha, integer(6) / integer(7));
        assert_eq!(
            proposal.step.to_rows(),
            vec![vec![Rat::zero(), integer(1) / integer(16)]]
        );
        let mut evidence = None;
        assert!(matches!(
            super::deposit::actual_epoch_face(
                LinearLocus::SourcePort(0),
                &proposal.step,
                &samples,
                &[],
                8,
                Rat::one(),
                &mut evidence
            ),
            Err(HnnError::Unadmitted { .. })
        ));
        assert_eq!(
            evidence.unwrap().condition,
            EpochStageCondition::ActualRayAlignment
        );
        let expected = law
            .news
            .add(&flow.covector)
            .unwrap()
            .subtract(&proposal.step.multiply(&proposal.successor.gram).unwrap())
            .unwrap();
        assert_eq!(
            proposal.successor.news, expected,
            "the successor retains Rstar-PH, never blended w-PH"
        );
    }

    #[test]
    fn joint_projection_preserves_the_declared_paired_map_and_exact_news() {
        let symmetry =
            PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0), None], &[0]).unwrap();
        let mut law = EpochLaw::founded_paired(2, 3, 3, 0, symmetry).unwrap();
        law.news = array(2, 3, 0, &[1, -1, 0, -1, 1, 0]);
        let samples = vec![
            Sample {
                weight: Rat::one(),
                feature: vec![Rat::one(), Rat::zero(), Rat::zero()],
                covector: vec![Rat::zero(), Rat::one()],
                masses: None,
            },
            Sample {
                weight: Rat::one(),
                feature: vec![Rat::zero(), Rat::one(), Rat::zero()],
                covector: vec![Rat::one(), Rat::zero()],
                masses: None,
            },
        ];
        let records: Vec<_> = samples
            .iter()
            .map(|sample| EpochRecord::from_sample(sample).unwrap())
            .collect();
        let flow = EpochFlow::from_records(2, 3, 3, 2, 0, 2, &records).unwrap();
        let opening = law.clone();
        let candidate = law
            .deposit_joint(&flow, &scalar(1), LinearLocus::Contrast(0), None, &mut None)
            .unwrap();
        assert_eq!(
            candidate.joint_direction.as_ref().unwrap().alpha,
            integer(1) / integer(2)
        );
        assert_eq!(candidate.eta_denominator, BigInt::one());
        assert!(!candidate.step.is_zero());
        let after = candidate.successor.map.to_rows();
        let remainder = candidate.successor.news.to_rows();
        for row in 0..2 {
            assert_eq!(after[row][0], after[1 - row][1]);
            assert_eq!(remainder[row][0], remainder[1 - row][1]);
            assert!(after[row][2].is_zero());
            assert!(remainder[row][2].is_zero());
        }
        let paired = flow.paired(law.declared_symmetry().unwrap()).unwrap();
        let target = law
            .map
            .multiply(&candidate.successor.gram)
            .unwrap()
            .add(&law.news)
            .unwrap()
            .add(&paired.covector)
            .unwrap();
        assert_eq!(
            candidate
                .successor
                .map
                .multiply(&candidate.successor.gram)
                .unwrap()
                .add(&candidate.successor.news)
                .unwrap(),
            target
        );
        assert_eq!(
            law, opening,
            "staging cannot publish into its immutable opening"
        );
    }

    #[test]
    fn joint_source_preflight_refines_for_a_bigint_divisor_without_retaining_it() {
        let mut law = EpochLaw::founded(1, 2, 3, 0).unwrap();
        let large = BigInt::one() << 80usize;
        law.gram =
            EpochArray::new(2, 2, 0, vec![1.into(), 0.into(), 0.into(), &large - 1]).unwrap();
        law.news = array(1, 2, 0, &[1, -1]);
        let samples = vec![
            Sample {
                weight: Rat::one(),
                feature: vec![Rat::one(), Rat::zero()],
                covector: vec![Rat::zero()],
                masses: None,
            },
            Sample {
                weight: Rat::one(),
                feature: vec![Rat::zero(), Rat::one()],
                covector: vec![Rat::one()],
                masses: None,
            },
        ];
        let records: Vec<_> = samples
            .iter()
            .map(|s| EpochRecord::from_sample(s).unwrap())
            .collect();
        let flow = EpochFlow::from_records(1, 2, 3, 2, 0, 2, &records).unwrap();
        let candidate = law
            .deposit_joint(
                &flow,
                &scalar(1),
                LinearLocus::SourcePort(0),
                Some((4, 1 << 20, 0, 0)),
                &mut None,
            )
            .unwrap();
        assert!(candidate.direction_divisor.bits() > 64);
        assert_eq!(candidate.eta_denominator, BigInt::one());
        assert_eq!(candidate.successor.map_lattice, 81);
        assert_eq!(
            candidate.step.to_rows(),
            vec![vec![
                integer(1) / Rat::from_integer(BigInt::one() << 81usize);
                2
            ]]
        );
        assert!(matches!(
            law.deposit_joint(
                &flow,
                &scalar(1),
                LinearLocus::SourcePort(0),
                Some((4, 64, 0, 0)),
                &mut None
            ),
            Err(HnnError::ConstitutionBudget { .. })
        ));
        let saved = candidate.successor.encode_checkpoint();
        assert!(!saved.contains("joint"));
        assert_eq!(
            EpochLaw::decode_checkpoint(&saved, &candidate.successor, 1 << 20).unwrap(),
            candidate.successor
        );
    }

    #[test]
    fn opposing_comparisons_obstruct_a_fresh_move_and_held_absorption_is_once() {
        let mut law = EpochLaw::founded(1, 1, 2, 0).unwrap();
        law.news = EpochArray::new(1, 1, 1, vec![(-3).into()]).unwrap();
        let sample = Sample {
            weight: Rat::one(),
            feature: vec![Rat::one()],
            covector: vec![integer(3) / integer(8)],
            masses: None,
        };
        let flow = EpochFlow::from_records(
            1,
            1,
            2,
            1,
            0,
            1,
            &[EpochRecord::from_sample(&sample).unwrap()],
        )
        .unwrap();
        let gain = scalar(1);
        let before = law.clone();
        let whole = law.deposit_source(&flow, &gain, 2, 1 << 20, 0, 0).unwrap();
        assert_eq!(
            whole.direction.scalar_ratio().unwrap(),
            -integer(9) / integer(16)
        );
        assert_eq!(whole.step.scalar_ratio().unwrap(), -integer(1) / integer(2));
        assert_eq!(whole.fall.scalar_ratio().unwrap(), integer(5) / integer(16));
        // The withdrawn fresh-only policy would propose +1/8. Keep the exact obstruction
        // without introducing that policy into the native material owner.
        let fresh_p = integer(1) / integer(8);
        let r_star = -integer(9) / integer(8);
        let normal_fall = &fresh_p * &r_star - &fresh_p * &fresh_p;
        let current_alignment = integer(3) / integer(8) * &fresh_p;
        assert_eq!(normal_fall, -integer(5) / integer(32));
        assert_eq!(current_alignment, integer(3) / integer(64));
        let joint = law
            .deposit_joint(
                &flow,
                &gain,
                LinearLocus::SourcePort(0),
                Some((2, 1 << 20, 0, 0)),
                &mut None,
            )
            .unwrap();
        assert_eq!(
            joint.joint_direction.as_ref().unwrap().alpha,
            integer(1) / integer(4)
        );
        assert!(joint.direction.is_zero());
        assert!(joint.step.is_zero());
        assert_eq!(joint.successor.map_lattice, law.map_lattice);
        assert_eq!(joint.successor.source_refinement, law.source_refinement);
        let held = law
            .deposit_source_at_eta(&flow, &gain, 2, 1 << 20, 0, 0, BigInt::zero())
            .unwrap();
        assert_eq!(
            joint.successor, held.successor,
            "a zero segment uses the same exact normal absorption, without invented material"
        );
        assert_eq!(held.successor.map, law.map);
        assert!(held.step.is_zero());
        assert_eq!(held.successor.gram.scalar_ratio().unwrap(), integer(2));
        assert_eq!(
            held.successor.news.scalar_ratio().unwrap(),
            -integer(9) / integer(8)
        );
        assert_eq!(held.successor.crossings, law.crossings + 1);
        let again = law
            .deposit_source_at_eta(&flow, &gain, 2, 1 << 20, 0, 0, BigInt::zero())
            .unwrap();
        assert_eq!(
            again.successor, held.successor,
            "discarded rungs never absorb this flow twice"
        );
        assert_eq!(law, before);
    }

    #[test]
    fn fresh_certificate_reads_the_grouped_flow_before_carried_news() {
        let state = EpochLaw::founded(2, 2, 32, 0).unwrap();
        let flow = EpochFlow::from_samples(2, 2, 32, 231, 0, &samples()).unwrap();
        let prepared = state.fresh(&flow).unwrap();
        let d = values(&prepared.direction);
        let g = values(&flow.covector);
        let delta_h = values(&flow.gram);
        let moved = product(&d, &delta_h);
        let mut alignment = Rat::zero();
        let mut moves = Rat::zero();
        for i in 0..2 {
            for j in 0..2 {
                alignment += &d[i][j] * &g[i][j];
                moves += &moved[i][j] * &d[i][j];
            }
        }
        assert_eq!(values(&prepared.alignment)[0][0], alignment);
        assert_eq!(values(&prepared.moves)[0][0], moves);
        assert!(alignment.is_positive());
        assert!(moves.is_positive());
        let mut carried = state.clone();
        carried.news = EpochArray::new(
            2,
            2,
            40,
            vec![
                BigInt::one() << 320usize,
                -BigInt::one(),
                BigInt::from(17),
                BigInt::from(-9),
            ],
        )
        .unwrap();
        let same = carried.fresh(&flow).unwrap();
        assert_eq!(same.direction, prepared.direction);
        assert_eq!(same.alignment, prepared.alignment);
        assert_eq!(same.moves, prepared.moves);
        assert_eq!(same.shares, prepared.shares);
        assert!(state.deposit(&flow, &scalar(-1)).is_err());
    }

    #[test]
    fn zero_representative_retains_news_and_widening_loses_nothing() {
        let state = EpochLaw::founded(1, 2, 32, 0).unwrap();
        let denominator = BigInt::one() << 70usize;
        let sample = EpochSample {
            feature: array(1, 2, 0, &[1, 0]),
            positive: array(1, 1, 0, &[1]),
            foil: EpochSeries {
                rows: 1,
                columns: 1,
                numerators: vec![&denominator - 1],
                denominator,
            },
            metric_weight: series(1, 1, &[0], 1),
        };
        let flow = EpochFlow::from_samples(1, 2, 32, 231, 0, &[sample]).unwrap();
        let result = state
            .identity_step(&flow, &scalar(1), BigInt::one(), BigInt::one())
            .unwrap();
        assert!(result.step.is_zero());
        assert!(result.fall.is_zero());
        assert_eq!(result.successor.news, flow.covector);
        assert!(!result.successor.news.is_zero());

        let wide: BigInt = (BigInt::one() << 320usize) + 8;
        let a = EpochArray::new(1, 2, 80, vec![wide.clone(), -wide]).unwrap();
        assert!(a.magnitude_limbs() > 2);
        let negative =
            EpochArray::new(1, 2, a.exponent, a.values.iter().map(|v| -v).collect()).unwrap();
        let canceled = a.add(&negative).unwrap();
        assert!(canceled.is_zero());
        assert_eq!(canceled.exponent, 0);
        assert_eq!(canceled.magnitude_limbs(), 0);
        let small = array(1, 2, 3, &[3, -5]);
        assert_eq!(a.add(&small).unwrap().subtract(&a).unwrap(), small);
    }

    #[test]
    fn receiver_partition_and_feature_admission_cannot_be_bypassed() {
        let state = EpochLaw::founded(2, 2, 32, 0).unwrap();
        let wrong = EpochFlow::from_samples(2, 2, 31, 231, 0, &samples()).unwrap();
        assert!(
            state
                .identity_step(&wrong, &scalar(1), BigInt::one(), BigInt::one())
                .is_err()
        );
        // Actual receiving ingress c can skip while this law has absorbed
        // no earlier batch. Its partition must still use that actual c.
        let late = EpochFlow::from_samples(2, 2, 32, 231, 3, &samples()).unwrap();
        assert_eq!(
            late.partition_exponent,
            partition_exponent(32, 231, 3).unwrap()
        );
        assert!(
            state
                .identity_step(&late, &scalar(1), BigInt::one(), BigInt::one())
                .is_ok()
        );
        let mut too_coarse = late.clone();
        too_coarse.partition_exponent -= 1;
        assert!(state.fresh(&too_coarse).is_err());
        assert!(state.deposit(&too_coarse, &scalar(1)).is_err());
        let mut false_bound = late.clone();
        false_bound.partition_cells = 1; // two heard faces cannot fit this declaration
        assert!(state.deposit(&false_bound, &scalar(1)).is_err());
        let mut unbounded_release = late.clone();
        unbounded_release.partitions[0].remainder_numerators[0] =
            unbounded_release.partitions[0].denominator.clone();
        assert!(state.deposit(&unbounded_release, &scalar(1)).is_err());
        let mut invalid = samples();
        invalid[0].feature = array(1, 2, 0, &[2, 1]);
        assert!(EpochFlow::from_samples(2, 2, 32, 231, 0, &invalid).is_err());
        let mut invalid = samples();
        invalid[0].metric_weight = series(1, 1, &[-1], 3);
        assert!(EpochFlow::from_samples(2, 2, 32, 231, 0, &invalid).is_err());
    }

    #[test]
    fn fresh_loci_join_the_current_tightened_certificate_before_absorption() {
        let field = crate::hnn::tests::learning::chain();
        let theta = Constitution::initial(&field, u64::MAX).unwrap();
        let readout = theta.receiving_law(2).unwrap().map();
        assert!(readout.entries().iter().all(Zero::is_zero));
        let reach = Reach {
            receiver: 2,
            stations: vec![1, 2],
            entries: vec![0],
            phases: 1,
            loci: crate::hnn::retention::loci(&field).into_iter().collect(),
            passages: Vec::new(),
        };
        let mut laws = Vec::new();
        let mut flows = Vec::new();
        let mut faces = Vec::new();
        for (kind, map) in [
            (LinearLocus::Receiving(2), readout),
            (
                LinearLocus::SourcePort(0),
                theta.source_law(0).unwrap().map(),
            ),
        ] {
            let (rows, columns) = (map.rows(), map.columns());
            let law = EpochLaw::founded(rows, columns, 32, 0).unwrap();
            let mut feature = EpochArray::zero(1, columns).unwrap();
            feature.values[0] = BigInt::one();
            let mut positive = EpochArray::zero(rows, 1).unwrap();
            positive.values[0] = BigInt::one();
            let sample = EpochSample {
                feature,
                positive,
                foil: EpochSeries {
                    rows,
                    columns: 1,
                    numerators: vec![BigInt::zero(); rows],
                    denominator: BigInt::one(),
                },
                metric_weight: series(1, 1, &[1], 1),
            };
            let flow = EpochFlow::from_samples(rows, columns, 32, 231, 0, &[sample]).unwrap();
            faces.push((
                kind,
                law.fresh(&flow)
                    .unwrap()
                    .certificate_face(&series(1, 1, &[1], 1))
                    .unwrap(),
            ));
            laws.push(law);
            flows.push(flow);
        }
        let cache = EpochSpectral::founded_zero(readout.rows(), readout.columns());
        let (steps, joint, _, _) = theta
            .certify_epoch_gains(&reach, &faces, &[], None, &cache)
            .unwrap();
        assert_eq!(steps.len(), 2);
        assert!(joint.as_ref().unwrap().holds());
        assert!(joint.as_ref().unwrap().certified_decrease() > Rat::zero());
        for (index, (kind, _)) in faces.iter().enumerate() {
            let reading = &steps[&(kind.locus(), Family::Map)];
            assert!(reading.step.step > Rat::zero());
            assert!(&reading.step.step * &reading.step.curvature <= reading.step.alignment);
            assert!(&reading.step.step * &reading.step.covector <= Rat::one());
            let exponent = reading.step.exponent;
            let gamma = if exponent >= 0 {
                EpochArray::new(1, 1, 0, vec![BigInt::one() << exponent as usize]).unwrap()
            } else {
                EpochArray::new(1, 1, (-exponent) as u32, vec![BigInt::one()]).unwrap()
            };
            let deposited = laws[index].deposit(&flows[index], &gamma).unwrap();
            assert!(!deposited.step.is_zero());
            assert!(deposited.fall.values[0] > BigInt::zero());
            assert_eq!(deposited.halvings, 0);
        }
    }
}

#[cfg(test)]
mod source_refinement_tests {
    use super::*;

    fn scalar(exponent: u32, value: i64) -> EpochArray {
        EpochArray::new(1, 1, exponent, vec![BigInt::from(value)]).unwrap()
    }

    fn flow(epoch: u64, orientation: i64) -> EpochFlow {
        EpochFlow {
            gram: scalar(0, 1),
            covector: scalar(2, orientation),
            support: vec![0],
            partitions: Vec::new(),
            cells: 1,
            partition_cells: 1,
            records: 1,
            partition_exponent: partition_exponent(11, 1, epoch).unwrap(),
            receiver_grain: 11,
            epoch,
        }
    }

    fn source(law: &EpochLaw, flow: &EpochFlow, gain: &EpochArray) -> EpochDeposit {
        law.deposit_source(flow, gain, law.map_lattice, 1 << 20, law.crossings, 0)
            .unwrap()
    }

    // This is a projection/retention control, not a native gain certificate or
    // learned-output fixture. The actual epoch consumer checks its final ray.
    #[test]
    fn recurrent_source_news_reaches_a_finer_material_grain_with_exact_remainder() {
        let declaration = EpochLaw::founded(1, 1, 11, 0).unwrap();
        let gain = scalar(13, 1);
        let mut fixed = declaration.clone();
        let mut adaptive = declaration;
        for epoch in 0..12 {
            let incoming = flow(epoch, 1);
            let old = fixed.deposit(&incoming, &gain).unwrap();
            assert!(old.step.is_zero());
            fixed = old.successor;
            let prepared = source(&adaptive, &incoming, &gain);
            assert!(!prepared.step.is_zero());
            assert!(prepared.fall.scalar_ratio().unwrap().is_positive());
            assert!(prepared.successor.map_lattice >= adaptive.map_lattice);
            assert!(prepared.successor.map.is_dyadic());
            let metric = adaptive.gram.add(&incoming.gram).unwrap();
            assert_eq!(
                prepared
                    .successor
                    .map
                    .multiply(&metric)
                    .unwrap()
                    .add(&prepared.successor.news)
                    .unwrap(),
                adaptive
                    .map
                    .multiply(&metric)
                    .unwrap()
                    .add(&adaptive.news)
                    .unwrap()
                    .add(&incoming.covector.scalar_product(&gain).unwrap())
                    .unwrap(),
            );
            if epoch == 0 {
                assert_eq!(prepared.successor.map_lattice, 16);
                assert_eq!(
                    prepared.step.scalar_ratio().unwrap(),
                    Rat::new(1.into(), BigInt::one() << 16usize)
                );
            }
            adaptive = prepared.successor;
        }
        assert!(!adaptive.news.is_zero());
        assert!(fixed.map.is_zero());
        assert!(!adaptive.map.is_zero());
    }

    #[test]
    fn signed_source_changes_cancel_and_zero_gain_holds_old_news() {
        let mut law = EpochLaw::founded(1, 1, 11, 0).unwrap();
        let gain = scalar(13, 1);
        for epoch in 0..8 {
            let orientation = if epoch % 2 == 0 { 1 } else { -1 };
            let prepared = source(&law, &flow(epoch, orientation), &gain);
            assert!(!prepared.step.is_zero());
            assert_eq!(
                prepared.step.values[0].sign(),
                BigInt::from(orientation).sign()
            );
            law = prepared.successor;
        }
        let old_news = law.news.clone();
        let held = source(&law, &flow(8, 1), &scalar(0, 0));
        assert!(held.step.is_zero());
        assert_eq!(held.successor.map, law.map);
        assert_eq!(held.successor.news, old_news);
        assert_eq!(held.successor.map_lattice, law.map_lattice);

        let mut cancellation = flow(8, 1);
        cancellation.covector = EpochArray::zero(1, 1)
            .unwrap()
            .subtract(&law.news.scalar_product(&scalar(0, 1 << 13)).unwrap())
            .unwrap();
        let cancelled = source(&law, &cancellation, &gain);
        assert!(cancelled.direction.is_zero());
        assert!(cancelled.step.is_zero());
        assert!(cancelled.successor.news.is_zero());
    }

    #[test]
    fn source_projection_budget_and_odd_rows_refuse_without_mutating_the_law() {
        let law = EpochLaw::founded(1, 1, 11, 0).unwrap();
        let before = law.clone();
        assert!(matches!(
            law.deposit_source(&flow(0, 1), &scalar(13, 1), 11, 1, 0, 0),
            Err(HnnError::ConstitutionBudget { .. }),
        ));
        assert_eq!(law, before);
        let mut odd = law.clone();
        odd.news = EpochArray::with_row_divisors(1, 1, 0, vec![1.into()], vec![3]).unwrap();
        assert!(
            odd.deposit_source(&flow(0, 1), &scalar(13, 1), 11, 1 << 20, 0, 0)
                .is_err()
        );
    }

    #[test]
    fn source_refinement_checkpoint_keeps_the_next_signed_step() {
        let gain = scalar(13, 1);
        let mut law = EpochLaw::founded(1, 1, 11, 0).unwrap();
        for epoch in 0..3 {
            law = source(&law, &flow(epoch, 1), &gain).successor;
        }
        assert!(!law.news.is_zero());
        let text = law.encode_checkpoint();
        let declaration = EpochLaw {
            source_refinement: true,
            ..EpochLaw::founded(1, 1, 11, 0).unwrap()
        };
        let cold = EpochLaw::decode_checkpoint(&text, &declaration, 1 << 20).unwrap();
        let next_flow = flow(3, -1);
        let uninterrupted = source(&law, &next_flow, &gain).successor;
        drop(law);
        let continued = source(&cold, &next_flow, &gain).successor;
        assert_eq!(continued, uninterrupted);
        assert_eq!(
            continued.encode_checkpoint(),
            uninterrupted.encode_checkpoint()
        );
        assert!(
            EpochLaw::decode_checkpoint(
                &text.replace("epoch-law-checkpoint-v3", "epoch-law-checkpoint-v2"),
                &declaration,
                1 << 20
            )
            .is_err()
        );
    }
}
