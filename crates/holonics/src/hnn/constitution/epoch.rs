//! One epoch's deposition: grouped exact series and the carried news `R = B - W H`.
//!
//! The computational object is the helical pair interaction. This owner changes a
//! constitution only at its receiver crossing; the helix, pair, faces and placement
//! remain the caller's. Precision is the receiver's tolerance partition, not an
//! authored machine width. Integer coordinates widen as their values require.

use super::*;

mod checkpoint;
mod flow;
mod spectral;
pub(crate) use flow::EpochRecord;
pub(crate) use spectral::EpochSpectral;

fn refused(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

fn extent() -> HnnError {
    ExactLinearError::ExtentOverflow.into()
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

/// An exact array on one shared dyadic denominator. The coordinates are never
/// individually reduced fractions. Removing common powers of two is exact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct EpochArray {
    pub(crate) rows: usize,
    pub(crate) columns: usize,
    pub(crate) exponent: u32,
    pub(crate) values: Vec<BigInt>,
}

impl EpochArray {
    pub(crate) fn new(
        rows: usize,
        columns: usize,
        exponent: u32,
        values: Vec<BigInt>,
    ) -> Result<Self, HnnError> {
        if rows.checked_mul(columns) != Some(values.len()) {
            return Err(refused("an epoch array must fill its declared shape"));
        }
        let mut array = Self {
            rows,
            columns,
            exponent,
            values,
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
            return;
        };
        let shift = common.min(u64::from(self.exponent)) as u32;
        if shift > 0 {
            for value in &mut self.values {
                *value >>= shift as usize;
            }
            self.exponent -= shift;
        }
    }

    fn same_shape(&self, other: &Self) -> Result<(), HnnError> {
        if (self.rows, self.columns) != (other.rows, other.columns) {
            return Err(refused("an epoch sum needs equal declared shapes"));
        }
        Ok(())
    }

    pub(crate) fn add(&self, other: &Self) -> Result<Self, HnnError> {
        self.same_shape(other)?;
        let exponent = self.exponent.max(other.exponent);
        let values = self
            .values
            .iter()
            .zip(&other.values)
            .map(|(a, b)| {
                (a << (exponent - self.exponent) as usize)
                    + (b << (exponent - other.exponent) as usize)
            })
            .collect();
        Self::new(self.rows, self.columns, exponent, values)
    }

    pub(crate) fn subtract(&self, other: &Self) -> Result<Self, HnnError> {
        let negative = Self::new(
            other.rows,
            other.columns,
            other.exponent,
            other.values.iter().map(|v| -v).collect(),
        )?;
        self.add(&negative)
    }

    pub(crate) fn multiply(&self, other: &Self) -> Result<Self, HnnError> {
        if self.columns != other.rows {
            return Err(refused("an epoch product needs matching ports"));
        }
        let exponent = self
            .exponent
            .checked_add(other.exponent)
            .ok_or_else(extent)?;
        let mut values =
            vec![BigInt::zero(); self.rows.checked_mul(other.columns).ok_or_else(extent)?];
        for i in 0..self.rows {
            for k in 0..self.columns {
                let left = &self.values[i * self.columns + k];
                if left.is_zero() {
                    continue;
                }
                for j in 0..other.columns {
                    values[i * other.columns + j] += left * &other.values[k * other.columns + j];
                }
            }
        }
        Self::new(self.rows, other.columns, exponent, values)
    }

    fn dot(&self, other: &Self) -> Result<Self, HnnError> {
        self.same_shape(other)?;
        Self::new(
            1,
            1,
            self.exponent
                .checked_add(other.exponent)
                .ok_or_else(extent)?,
            vec![
                self.values
                    .iter()
                    .zip(&other.values)
                    .map(|(a, b)| a * b)
                    .sum(),
            ],
        )
    }

    fn half(&self) -> Result<Self, HnnError> {
        Self::new(
            self.rows,
            self.columns,
            self.exponent.checked_add(1).ok_or_else(extent)?,
            self.values.clone(),
        )
    }

    fn scalar_product(&self, scalar: &Self) -> Result<Self, HnnError> {
        if (scalar.rows, scalar.columns) != (1, 1) {
            return Err(refused("an epoch scalar has one coordinate"));
        }
        Self::new(
            self.rows,
            self.columns,
            self.exponent
                .checked_add(scalar.exponent)
                .ok_or_else(extent)?,
            self.values.iter().map(|v| v * &scalar.values[0]).collect(),
        )
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.values.iter().all(Zero::is_zero)
    }

    /// Required magnitude limbs, derived from the actual common coordinates.
    pub(crate) fn magnitude_limbs(&self) -> u64 {
        self.values
            .iter()
            .map(BigInt::bits)
            .max()
            .unwrap_or(0)
            .div_ceil(64)
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
    pub(crate) records: u64,
    pub(crate) partition_exponent: u32,
    pub(crate) receiver_grain: u32,
    pub(crate) epoch: u64,
}

impl EpochFlow {
    /// The existing paired-port admission and orthogonal half-sum, applied to the
    /// whole epoch. Outside columns are never reached; the diagonal prior keeps
    /// them uncoupled, so the exact news update preserves the partial family too.
    fn paired(&self, symmetry: &PortSymmetry) -> Result<Self, HnnError> {
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
            covector: EpochArray::new(
                rows,
                columns,
                self.covector.exponent.checked_add(1).ok_or_else(extent)?,
                covector,
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
    pub(crate) crossings: u64,
    /// This bound affects future certified gains, so a continuing checkpoint
    /// carries it with W/H/R rather than reconstructing a different schedule.
    pub(crate) spectral: EpochSpectral,
    symmetry: Option<PortSymmetry>,
}

#[derive(Clone, Debug)]
pub(crate) struct EpochDeposit {
    pub(crate) successor: EpochLaw,
    pub(crate) step: EpochArray,
    pub(crate) fall: EpochArray,
    pub(crate) eta_numerator: BigInt,
    pub(crate) eta_denominator: BigInt,
    pub(crate) halvings: u64,
    pub(crate) direction: EpochArray,
    pub(crate) shares: Vec<i64>,
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
        let unit = IntegralMatrix::from_grouped(
            self.direction.rows,
            self.direction.columns,
            self.direction.values.clone(),
            BigInt::one() << self.direction.exponent as usize,
        )?;
        let scalar = |value: &EpochArray| {
            Rat::new(
                value.values[0].clone(),
                BigInt::one() << value.exponent as usize,
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
        )?
        .map_err(|_| refused("the native epoch certificate returned a candidate refusal"))
    }
}

impl EpochLaw {
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
        let width = u64::try_from(columns).map_err(|_| extent())?;
        Ok(Self {
            map: EpochArray::zero(rows, columns)?,
            gram,
            news: EpochArray::zero(rows, columns)?,
            receiver_grain,
            map_lattice: receiver_grain
                .checked_add(ceil_log2_count(width))
                .ok_or_else(extent)?,
            crossings: 0,
            spectral: EpochSpectral::founded_zero(rows, columns),
            symmetry: None,
        })
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
            EpochArray::new(news.rows, columns, exponent, values)?,
            shares,
        ))
    }

    pub(crate) fn fresh(&self, flow: &EpochFlow) -> Result<EpochFresh, HnnError> {
        if flow.epoch != self.crossings || flow.receiver_grain != self.receiver_grain {
            return Err(refused(
                "fresh epoch news must use its life's receiver partition",
            ));
        }
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
        if gamma.values.iter().any(Signed::is_negative) {
            return Err(refused(
                "the epoch's certified fresh-news gain is nonnegative",
            ));
        }
        self.deposited_at(flow, gamma, BigInt::one(), BigInt::one())
    }

    fn deposited_at(
        &self,
        flow: &EpochFlow,
        gamma: &EpochArray,
        eta_numerator: BigInt,
        eta_denominator: BigInt,
    ) -> Result<EpochDeposit, HnnError> {
        if eta_numerator.is_negative() || !eta_denominator.is_positive() {
            return Err(refused(
                "an epoch certificate needs a nonnegative step ratio",
            ));
        }
        if flow.epoch != self.crossings || flow.receiver_grain != self.receiver_grain {
            return Err(refused(
                "an epoch flow must use its life's receiver partition",
            ));
        }
        let paired = self.symmetry.as_ref().map(|s| flow.paired(s)).transpose()?;
        let flow = paired.as_ref().unwrap_or(flow);
        self.gram.same_shape(&flow.gram)?;
        self.map.same_shape(&flow.covector)?;
        let gram = self.gram.add(&flow.gram)?;
        let news = self.news.add(&flow.covector.scalar_product(gamma)?)?;
        let (direction, shares) = self.direction(&news, &gram, &flow.support)?;
        let shift = i64::from(self.map_lattice) - i64::from(direction.exponent);
        let denominator = if shift < 0 {
            &eta_denominator << (-shift) as usize
        } else {
            eta_denominator.clone()
        };
        let values = direction
            .values
            .iter()
            .map(|v| {
                let numerator = v * &eta_numerator;
                let numerator = if shift > 0 {
                    numerator << shift as usize
                } else {
                    numerator
                };
                numerator / &denominator
            })
            .collect();
        let step = EpochArray::new(self.map.rows, self.map.columns, self.map_lattice, values)?;
        let linear = step.dot(&news)?;
        let quadratic = step.multiply(&gram)?.dot(&step)?.half()?;
        let fall = linear.subtract(&quadratic)?;
        if !step.is_zero() && !fall.values[0].is_positive() {
            return Err(HnnError::EpochStepNonDescending {
                crossing: self.crossings,
            });
        }
        let map = self.map.add(&step)?;
        let news = news.subtract(&step.multiply(&gram)?)?;
        let mut spectral = self.spectral.clone();
        spectral.observe_move(&step)?;
        let successor = Self {
            map,
            gram,
            news,
            spectral,
            crossings: self.crossings.checked_add(1).ok_or_else(extent)?,
            ..self.clone()
        };
        Ok(EpochDeposit {
            successor,
            step,
            fall,
            eta_numerator,
            eta_denominator,
            halvings: 0,
            direction,
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
            .map(|row| {
                row.iter()
                    .map(|n| Rat::new(n.clone(), denominator.clone()))
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
        let late = EpochFlow::from_samples(2, 2, 32, 231, 1, &samples()).unwrap();
        assert!(
            state
                .identity_step(&late, &scalar(1), BigInt::one(), BigInt::one())
                .is_err()
        );
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
