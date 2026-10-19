//! Exact, explicitly hypothetical one-epoch normal-law readout.
//!
//! This module does not claim access to the listener's private `PreparedStep.unit`, persistent
//! carry, or a device-certified gain. It forms `G_cross` from the retained frozen comparison
//! covectors and staged samples, then reports the unit-gain (`gamma = 1`) hypothetical law with
//! zero incoming residual. The native material Gram is the metric; the separately retained Gram
//! remainder is shown as carry and is never silently added to that metric.

#[path = "exact_digest.rs"]
mod exact_digest;

use super::*;
use holonics::hnn::constitution::NormalLaw;
use holonics::hnn::paired::PortSymmetry;
use holonics::hnn::ratio::Face;
use holonics::hnn::reference::FrozenComparison;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::fmt;

type Matrix = ExactRatMatrix;

/// Ephemeral products already formed by a branch report, retained for later intervention output.
/// This is report-local caching, not native state or a persistent listener receipt.
#[derive(Default)]
pub(super) struct ReportCapture {
    pub(super) gradient: Option<Matrix>,
    pub(super) exact_metric_scale: Option<Rat>,
}

/// Source binding for the ordinary listener's receiver clock (R12 §3's founding clock,
/// and Opus 6fd3d3a248954408bbaf128ff701a8c4: c is read at the span's opening).
///
/// Ring 0 advances once for every admitted class; rings 1 and 2 advance only by the preceding
/// carry. Consequently a ring-2 ingress tick closes one lower-two-ring interval. `c` counts those
/// successful ingress ticks from the fresh mount, including shortened intervals after rekey;
/// it is neither ring 2's full winding, a physical Word's ticks, nor a quotient of source length.
/// The receipt counter must travel with a restored opening or the binding is unavailable.
///
/// The next interval has at most d0*d1 cells. An uninterrupted d0*d1-cell passage visits every
/// lower-two-ring residue once; a rekey inside that passage invalidates this coverage statement.
/// This helper establishes the uniform ordinary lock route only: located occurrence digits and
/// other receiver/clock families require their own binding. It does not supply a precision b.
pub(super) fn opening_partition_context(
    field: &Field,
    actual_ingress_ticks: Option<u64>,
) -> Result<(u64, u64)> {
    let epoch_index = actual_ingress_ticks.ok_or(
        "receiver epoch index unavailable: the opening lacks its successful-ingress counter from the fresh mount",
    )?;
    if field.rings().len() != 3
        || field.sources() != [0]
        || field.receivers().len() != 1
        || field.receivers()[0].ring != 2
        || field.receivers()[0].aperture != 1
        || field.alphabet() == 0
        || field
            .rings()
            .iter()
            .any(|ring| ring.advance() != holonics::hnn::RingAdvance::Lock)
    {
        return Err("receiver partition binding requires the ordinary three-ring Lock chain, source 0, and one aperture-one receiver on ring 2".into());
    }
    for class in 0..field.alphabet() {
        if field.class_advance(0, class)? != 1
            || field.class_advance(1, class)? != 0
            || field.class_advance(2, class)? != 0
        {
            return Err("receiver partition binding refuses a class-dependent or directly driven later-ring clock".into());
        }
    }
    let cell_bound =
        receiver_partition_cell_bound(field.rings()[0].period(), field.rings()[1].period())?;
    Ok((epoch_index, cell_bound))
}

fn receiver_partition_cell_bound(first_period: u64, second_period: u64) -> Result<u64> {
    if first_period < 2 || second_period < 2 {
        return Err("receiver partition requires two admitted closing rotor periods".into());
    }
    first_period
        .checked_mul(second_period)
        .ok_or_else(|| "receiver partition period product overflows u64".into())
}

/// The amended face partition owes half a receiver cell (Opus 837fb12cbb2341e790cfc73480140467,
/// upheld by cf792f6d763d4897a6c2ea19e09032b2): b_R = ceil(log2(2 L_R)), where L_R is the native
/// receiver_grain denominator. This is a conversion of units, never a cast of that denominator
/// to a bit exponent. Zero has no receiver cell. Non-powers round upward, so 2^(-b_R) <= 1/(2 L_R).
/// Multiplication widens to u128 before doubling: every u64 grain is admitted without overflow,
/// and the largest possible exponent is 65. This read changes no native tolerance or lattice.
pub(super) fn amended_partition_receiver_exponent(receiver_grain: u64) -> Result<u32> {
    if receiver_grain == 0 {
        return Err(
            "amended partition requires a positive native receiver grain denominator".into(),
        );
    }
    let doubled = u128::from(receiver_grain) * 2;
    Ok(u128::BITS - (doubled - 1).leading_zeros())
}

/// Require the exponent supplied by the actual opening's grain conversion. An opening without
/// that source binding still refuses; the native face-grain denominator is not an exponent.
pub(super) fn require_partition_precision(amended_exponent: Option<u32>) -> Result<u32> {
    amended_exponent.ok_or_else(|| {
        "compact stall report unavailable: opening lacks amended_partition_receiver_exponent(native_receiver_grain); the native face-grain denominator is not an exponent".into()
    })
}

#[derive(Clone, Copy)]
struct PartitionContext {
    receiver_exponent: u32,
    /// Declared heard-sample bound at this aperture-one receiving map. The live adapter checks
    /// actual samples per cell before using the clock interval's bound for these records.
    cell_bound: u64,
    /// c is the source-bound ring-2 ingress tick count from founding, snapped at the span opening.
    epoch_index: u64,
    phase_period: u64,
}

fn partition_exponent_explicit(context: PartitionContext) -> Result<u32> {
    if context.cell_bound == 0 {
        return Err("a face partition requires its declared positive heard-sample bound".into());
    }
    if context.phase_period == 0 {
        return Err(
            "a face partition requires its declared positive receiving phase period".into(),
        );
    }
    let ceil_log2 = |n: u64| {
        if n <= 1 {
            0
        } else {
            u64::BITS - (n - 1).leading_zeros()
        }
    };
    let next = context
        .epoch_index
        .checked_add(1)
        .ok_or("partition epoch index overflows its next crossing")?;
    context
        .receiver_exponent
        .checked_add(ceil_log2(context.cell_bound))
        .and_then(|l| l.checked_add(1))
        .and_then(|l| l.checked_add(2 * ceil_log2(next)))
        .ok_or_else(|| "receiver-derived partition exponent overflows u32".into())
}

/// A receiving sample after its exact frozen one-hot comparison has been checked. Its foil
/// stays undivided as nonnegative integer weights and their positive common normalizer.
struct PartitionSample {
    feature: Vec<Rat>,
    weights: Vec<BigInt>,
    normalizer: BigInt,
    target: usize,
    /// One exact already-produced phase covector per class. It is never partitioned.
    phase: Vec<Rat>,
}

struct FaceRelease {
    quotient: Vec<BigInt>,
    remainder: Vec<BigInt>,
    denominator: BigInt,
}

struct PartitionedStatistics {
    positive: Matrix,
    foil: Matrix,
    phase: Matrix,
    gradient: Matrix,
    gram_delta: Matrix,
    releases: Vec<FaceRelease>,
    exponent: u32,
    /// Strict bound on each magnitude entry's omitted contribution after the class scale.
    /// Projection is an orthogonal half-sum, so this common absolute bound is preserved.
    released_entry_bound: Rat,
}

fn face_integer_weights(face: &Face) -> Result<(Vec<BigInt>, BigInt)> {
    let bottom = face
        .cells()
        .iter()
        .map(|cell| &cell.carry)
        .min()
        .ok_or("a frozen comparison face has no classes")?;
    let mut weights = Vec::with_capacity(face.cells().len());
    for cell in face.cells() {
        if cell.phase >= face.grain() {
            return Err("a frozen face has a phase outside its declared grain".into());
        }
        let exponent = usize::try_from(&cell.carry - bottom)
            .map_err(|_| "a frozen face's exact carry difference does not fit an address")?;
        weights.push((BigInt::from(face.grain()) + BigInt::from(cell.phase)) << exponent);
    }
    let normalizer: BigInt = weights.iter().sum();
    if !normalizer.is_positive() {
        return Err("a frozen face requires a positive integer normalizer".into());
    }
    Ok((weights, normalizer))
}

fn checked_partition_sample(
    sample: &Sample,
    covector: &[Rat],
    face: &Face,
) -> Result<PartitionSample> {
    let classes = face.cells().len();
    if sample.weight != Rat::one() || covector.len() != 2 * classes {
        return Err(
            "partitioned receiving statistics require exact unit-weight complex samples".into(),
        );
    }
    let (weights, normalizer) = face_integer_weights(face)?;
    let mut target = None;
    for (class, weight) in weights.iter().enumerate() {
        let q = Rat::new(weight.clone(), normalizer.clone()) + &covector[2 * class];
        if q == Rat::one() && target.is_none() {
            target = Some(class);
        } else if !q.is_zero() {
            return Err("frozen one-hot target reconstruction failed; a soft or foreign covector cannot set q".into());
        }
    }
    Ok(PartitionSample {
        feature: sample.feature.clone(),
        weights,
        normalizer,
        target: target.ok_or("the frozen comparison has no one-hot target")?,
        phase: covector.iter().skip(1).step_by(2).cloned().collect(),
    })
}

fn dyadic_feature(value: &Rat) -> bool {
    value.denom().is_positive()
        && value
            .denom()
            .trailing_zeros()
            .is_some_and(|zeros| value.denom().bits() == zeros + 1)
}

/// Read-only use of the existing native integer outer-product owner. Positive, partitioned foil
/// and phase samples are accumulated independently by NormalLaw::projected_statistics, whose
/// integral/outer_integral path sums integer coordinates over common denominators. Only these
/// completed series become rational matrix views; individual unpartitioned p_tilde never sum
/// into G. This neither publishes phase4's native owner nor changes a deposition law.
fn partitioned_statistics(
    law: &NormalLaw,
    samples: &[PartitionSample],
    context: PartitionContext,
    metric_scale: Option<&Rat>,
    mut checkpoint: impl FnMut() -> Result<()>,
) -> Result<PartitionedStatistics> {
    checkpoint()?;
    let count = u64::try_from(samples.len()).map_err(|_| "partition sample count overflows u64")?;
    if count > context.cell_bound {
        return Err("actual partition sample count exceeds the declared heard-sample bound".into());
    }
    let exponent = partition_exponent_explicit(context)?;
    let lattice_denominator = BigInt::one() << exponent as usize;
    let classes = law.map().rows() / 2;
    if law.map().rows() != 2 * classes || classes == 0 {
        return Err("receiving partition requires nonempty complex class rows".into());
    }
    let scale = metric_scale.cloned().unwrap_or_else(Rat::one);
    if !scale.is_positive()
        || !dyadic_feature(&scale)
        || (!scale.numer().is_one()
            && scale
                .numer()
                .trailing_zeros()
                .is_none_or(|zeros| scale.numer().bits() != zeros + 1))
    {
        return Err("the receiving class metric must be its native positive power of two".into());
    }
    let mut positive = Vec::with_capacity(samples.len());
    let mut foil = Vec::with_capacity(samples.len());
    let mut phase = Vec::with_capacity(samples.len());
    let mut releases = Vec::with_capacity(samples.len());
    let mut max_feature = Rat::zero();
    for sample in samples {
        checkpoint()?;
        if sample.feature.len() != law.map().columns()
            || sample.weights.len() != classes
            || sample.phase.len() != classes
            || sample.target >= classes
            || !sample.normalizer.is_positive()
            || sample.weights.iter().any(Signed::is_negative)
            || sample.weights.iter().sum::<BigInt>() != sample.normalizer
            || sample
                .feature
                .iter()
                .any(|f| !dyadic_feature(f) || f.abs() > Rat::one())
        {
            return Err("partition sample disagrees with its unit-weight, bounded dyadic producer or exact integer face".into());
        }
        // The phase series retains only the receiving period's fixed odd factor beside
        // powers of two. A foreign denominator cannot silently widen this native contract.
        if sample.phase.iter().any(|value| {
            let twos = value.denom().trailing_zeros().unwrap_or(0);
            let odd = value.denom() >> twos as usize;
            !(BigInt::from(context.phase_period) % odd).is_zero()
        }) {
            return Err(
                "phase covector denominator leaves the receiving period's declared odd factor"
                    .into(),
            );
        }
        max_feature = max_feature.max(
            sample
                .feature
                .iter()
                .map(Rat::abs)
                .max()
                .unwrap_or_else(Rat::zero),
        );
        let mut q = vec![Rat::zero(); 2 * classes];
        let mut p_hat = q.clone();
        let mut whole_phase = q.clone();
        q[2 * sample.target] = Rat::one();
        let mut quotient = Vec::with_capacity(classes);
        let mut remainder = Vec::with_capacity(classes);
        for class in 0..classes {
            let scaled = &sample.weights[class] << exponent as usize;
            let retained = &scaled / &sample.normalizer;
            let released = &scaled - &retained * &sample.normalizer;
            if released.is_negative() || released >= sample.normalizer {
                return Err("exact face division did not return its Euclidean remainder".into());
            }
            p_hat[2 * class] = Rat::new(retained.clone(), lattice_denominator.clone());
            whole_phase[2 * class + 1] = sample.phase[class].clone();
            quotient.push(retained);
            remainder.push(released);
        }
        let make = |covector| Sample {
            weight: Rat::one(),
            feature: sample.feature.clone(),
            covector,
            masses: None,
        };
        positive.push(make(q));
        foil.push(make(p_hat));
        phase.push(make(whole_phase));
        releases.push(FaceRelease {
            quotient,
            remainder,
            denominator: sample.normalizer.clone(),
        });
    }
    checkpoint()?;
    let (positive, gram_delta) = law.projected_statistics(&positive)?;
    checkpoint()?;
    let (foil, _) = law.projected_statistics(&foil)?;
    checkpoint()?;
    let (phase, _) = law.projected_statistics(&phase)?;
    checkpoint()?;
    let mut gradient = matrix_subtract(&positive, &foil)?.to_rows();
    for (row_index, row) in gradient.iter_mut().enumerate() {
        for (column, entry) in row.iter_mut().enumerate() {
            *entry = &*entry * &scale + phase.get(row_index, column)?;
        }
    }
    let released_entry_bound = &scale * Rat::from_integer(BigInt::from(count)) * max_feature
        / Rat::from_integer(lattice_denominator);
    checkpoint()?;
    Ok(PartitionedStatistics {
        positive,
        foil,
        phase,
        gradient: Matrix::new(gradient)?,
        gram_delta,
        releases,
        exponent,
        released_entry_bound,
    })
}

/// The ordinary one-phase comparison emits at most one receiving sample per heard cell.
/// Check the actual capture before transferring its clock interval bound to the sample sum;
/// record multiplicity at source/contrast loci cannot use this receiving-only adapter.
fn checked_heard_sample_population(
    samples_per_cell: &[usize],
    declared_heard_sample_bound: u64,
) -> Result<u64> {
    if declared_heard_sample_bound == 0 {
        return Err("receiving samples require a positive declared heard-sample bound".into());
    }
    let mut actual_samples = 0u64;
    for &samples in samples_per_cell {
        let samples =
            u64::try_from(samples).map_err(|_| "actual receiving sample count exceeds u64")?;
        actual_samples = actual_samples
            .checked_add(samples)
            .ok_or("actual receiving sample population overflows u64")?;
    }
    if actual_samples > declared_heard_sample_bound {
        return Err("actual receiving sample count exceeds the declared heard-sample bound".into());
    }
    if samples_per_cell.iter().any(|&samples| samples > 1) {
        return Err(
            "receiving sample multiplicity exceeds the source-bound aperture-one comparison".into(),
        );
    }
    Ok(actual_samples)
}

fn partitioned_crossing_statistics(
    branch: &str,
    crossing: &CutView,
    views: &[CutView],
    budget: &timing::ReportBudget,
) -> Result<(PartitionedStatistics, Option<Rat>)> {
    let receiver_exponent = require_partition_precision(crossing.receiver_partition_exponent)?;
    let context = PartitionContext {
        receiver_exponent,
        cell_bound: crossing.partition_cell_bound.ok_or("compact stall report unavailable: opening partition cell bound is not source-bound")?,
        epoch_index: crossing.partition_epoch_index.ok_or("compact stall report unavailable: opening lacks its persisted ring-2 ingress tick count from founding")?,
        phase_period: views.first().and_then(|view| {
            view.frozen.as_ref().and_then(|frozen| view.pre_clocks.get(frozen.ratio().phases().ring()).map(|clock| clock.0))
        }).ok_or("partitioned phase series requires its actual receiving clock period")?,
    };
    let samples_per_cell = views
        .iter()
        .map(|view| view.samples.len())
        .collect::<Vec<_>>();
    let actual_samples = checked_heard_sample_population(&samples_per_cell, context.cell_bound)?;
    println!(
        "step0_epoch_sample_population branch={branch} declared_heard_sample_bound={} actual_heard_cells={} actual_samples={actual_samples} samples_per_cell={samples_per_cell:?} source=actual-staged-receiving-records; aperture_one_multiplicity_checked=true; unit_weight_admission=required-before-sum",
        context.cell_bound,
        views.len()
    );
    let mut records = Vec::new();
    let mut metric_samples = Vec::new();
    for view in views {
        budget.check_before_work("partitioned crossing comparison provenance")?;
        let frozen = view.frozen.as_ref().ok_or(
            "partitioned crossing statistics require the actual frozen one-hot comparison",
        )?;
        if frozen.ratio().phases().ring() != 2 || frozen.ratio().phases().aperture() != 1 {
            return Err(
                "receiving sample bound requires the actual ring-2 aperture-one comparison".into(),
            );
        }
        let wave = super::held_wave(
            &crossing.map,
            &view.producing_map,
            frozen.wave(),
            &view.samples,
        )?;
        let covectors = frozen.recompare_covector(&wave)?;
        if covectors != view.crossing_covectors || covectors.len() != view.samples.len() {
            return Err(
                "partitioned crossing covectors do not match their retained producing comparison"
                    .into(),
            );
        }
        let combined = frozen.combined_faces(&wave)?;
        if combined.faces.len() != view.samples.len() {
            return Err("partitioned crossing faces do not align with staged samples".into());
        }
        for ((sample, covector), face) in view.samples.iter().zip(&covectors).zip(&combined.faces) {
            records.push(checked_partition_sample(sample, covector, face)?);
            let mut metric = sample.clone();
            metric.covector = covector.clone();
            // Carry the face's actual masses into the native class-metric owner; reconstructing
            // them from the newly partitioned q-p_hat would silently change the metric.
            metric.masses = Some(face.odometer_masses()?);
            metric_samples.push(metric);
        }
    }
    let scale = receiving_class_metric(&metric_samples);
    let statistics =
        partitioned_statistics(&crossing.law, &records, context, scale.as_ref(), || {
            budget.check_before_work("partitioned native integer series")?;
            Ok(())
        })?;
    Ok((statistics, scale))
}

fn rat_pow2(exponent: i64) -> Rat {
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << exponent as usize)
    } else {
        Rat::new(BigInt::one(), BigInt::one() << (-exponent) as usize)
    }
}

fn ceil_log2_positive(value: &Rat) -> Option<i64> {
    if value <= &Rat::zero() {
        return None;
    }
    let numerator = value.numer().bits() as i64;
    let denominator = value.denom().bits() as i64;
    let candidate = numerator - denominator;
    Some(if value <= &rat_pow2(candidate) {
        candidate
    } else {
        candidate + 1
    })
}

fn matrix_is_symmetric(matrix: &Matrix) -> bool {
    matrix.is_square()
        && (0..matrix.rows())
            .all(|i| (0..matrix.columns()).all(|j| matrix.get(i, j).ok() == matrix.get(j, i).ok()))
}

fn matrix_max_abs(matrix: &Matrix) -> Rat {
    matrix
        .entries()
        .iter()
        .map(|entry| entry.abs())
        .max()
        .unwrap_or_else(Rat::zero)
}

fn leading_determinant(matrix: &Matrix, extent: usize) -> Option<Rat> {
    if extent == 0 || extent > matrix.rows() || !matrix.is_square() {
        return (extent == 0).then(|| Rat::one());
    }
    let mut values = (0..extent)
        .map(|i| {
            (0..extent)
                .map(|j| matrix.get(i, j).ok().cloned())
                .collect::<Option<Vec<_>>>()
        })
        .collect::<Option<Vec<_>>>()?;
    let mut determinant = Rat::one();
    for pivot in 0..extent {
        let selected = (pivot..extent).find(|&row| !values[row][pivot].is_zero())?;
        if selected != pivot {
            values.swap(selected, pivot);
            determinant = -determinant;
        }
        let diagonal = values[pivot][pivot].clone();
        determinant *= &diagonal;
        for row in (pivot + 1)..extent {
            let factor = &values[row][pivot] / &diagonal;
            for column in (pivot + 1)..extent {
                let correction = &factor * &values[pivot][column];
                values[row][column] -= correction;
            }
        }
    }
    Some(determinant)
}

fn is_positive_definite(matrix: &Matrix) -> bool {
    matrix.is_square()
        && matrix_is_symmetric(matrix)
        && (1..=matrix.rows()).all(|extent| {
            leading_determinant(matrix, extent).is_some_and(|determinant| determinant > Rat::zero())
        })
}

fn unconstrained_reasons(
    crossing_support: &[usize],
    crossing_width: usize,
    end_support: &[usize],
    end_width: usize,
    gram: &Matrix,
) -> Vec<&'static str> {
    let full_support = |support: &[usize], width: usize| {
        support.len() == width && support.iter().copied().eq(0..width)
    };
    let mut reasons = Vec::new();
    if !matrix_is_symmetric(gram) {
        reasons.push("H_end is not exactly symmetric");
    }
    if !is_positive_definite(gram) {
        reasons.push("H_end positive-definiteness is not established");
    }
    if !full_support(crossing_support, crossing_width)
        || !full_support(end_support, end_width)
        || crossing_support != end_support
    {
        reasons.push("receiver chart support is not the same full declared coordinate set");
    }
    reasons
}

fn map_respects_native_subspace(law: &NormalLaw, map: &Matrix) -> Result<bool> {
    match law.symmetry() {
        Some(symmetry) => Ok(symmetry.first_failure(map)?.is_none()),
        None => Ok(true),
    }
}

fn gram_commutes_with_native_symmetry(law: &NormalLaw, gram: &Matrix) -> bool {
    law.symmetry()
        .is_none_or(|symmetry| gram_commutes_with_symmetry(symmetry, gram))
}

fn gram_commutes_with_symmetry(symmetry: &PortSymmetry, gram: &Matrix) -> bool {
    gram.is_square()
        && symmetry.columns().len() == gram.rows()
        && (0..gram.rows()).all(|row| {
            (0..gram.columns()).all(|column| {
                gram.get(row, column).ok()
                    == gram.get(symmetry.column(row), symmetry.column(column)).ok()
            })
        })
}

pub(super) fn spec_lattice_exponent(receiver_grain: u64, support_width: usize) -> Result<u32> {
    let b_r = amended_partition_receiver_exponent(receiver_grain)?;
    if support_width == 0 {
        return Err("specification LW requires nonzero support width".into());
    }
    let width = u64::try_from(support_width).map_err(|_| "support width exceeds u64")?;
    let ceil_width = u64::BITS - (width - 1).leading_zeros();
    b_r.checked_add(ceil_width)
        .ok_or_else(|| "specification LW overflows u32".into())
}

/// The specification comparison uses the explicitly stored solved-chart support. An empty
/// block is valid: the native chart still acts by its scaled identity on every declared map
/// coordinate. The comparison's log2(0) is undefined; it supplies no substitute exponent/unit
/// and does not prevent independent native-lattice or matrix readings.
#[derive(Debug, Eq, PartialEq)]
enum SpecificationLatticeReadout {
    UndefinedEmptySolvedSupport {
        declared_width: usize,
        receiver_exponent: u32,
    },
    Defined {
        declared_width: usize,
        support_width: usize,
        receiver_exponent: u32,
        exponent: u32,
        unit: Rat,
        native_cross_mismatch: bool,
        native_end_mismatch: bool,
    },
}

fn specification_lattice_readout(
    receiver_grain: u64,
    support: &[usize],
    declared_width: usize,
    native_lw_cross: u32,
    native_lw_end: u32,
) -> Result<SpecificationLatticeReadout> {
    let receiver_exponent = amended_partition_receiver_exponent(receiver_grain)?;
    if declared_width == 0 {
        return Err(
            "specification lattice report requires positive declared receiver width".into(),
        );
    }
    if support
        .iter()
        .any(|&coordinate| coordinate >= declared_width)
        || support.windows(2).any(|pair| pair[0] >= pair[1])
    {
        return Err(
            "specification lattice report requires ordered solved support within receiver width"
                .into(),
        );
    }
    if support.is_empty() {
        return Ok(SpecificationLatticeReadout::UndefinedEmptySolvedSupport {
            declared_width,
            receiver_exponent,
        });
    }
    let exponent = spec_lattice_exponent(receiver_grain, support.len())?;
    Ok(SpecificationLatticeReadout::Defined {
        declared_width,
        support_width: support.len(),
        receiver_exponent,
        exponent,
        unit: rat_pow2(-i64::from(exponent)),
        native_cross_mismatch: native_lw_cross != exponent,
        native_end_mismatch: native_lw_end != exponent,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SilenceVerdict {
    BelowGrain,
    AtOrAboveWholeGrain,
}

fn silence_verdict(bound: &Rat, grain: &Rat) -> SilenceVerdict {
    if bound < grain {
        SilenceVerdict::BelowGrain
    } else {
        SilenceVerdict::AtOrAboveWholeGrain
    }
}

#[derive(Debug)]
struct NonpositiveHypotheticalFall {
    fall: Rat,
}

impl fmt::Display for NonpositiveHypotheticalFall {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "nonzero hypothetical step has nonpositive exact fall {} under the admitted unconstrained metric",
            self.fall
        )
    }
}

impl std::error::Error for NonpositiveHypotheticalFall {}

fn check_hypothetical_fall(
    nonzero_step: bool,
    unconstrained_metric_admitted: bool,
    fall: &Rat,
) -> std::result::Result<(), NonpositiveHypotheticalFall> {
    if nonzero_step && unconstrained_metric_admitted && fall <= &Rat::zero() {
        Err(NonpositiveHypotheticalFall { fall: fall.clone() })
    } else {
        Ok(())
    }
}

fn matrix_product(left: &Matrix, right: &Matrix) -> Result<Matrix> {
    if left.columns() != right.rows() {
        return Err("epoch matrix product dimensions disagree".into());
    }
    let mut rows = vec![vec![Rat::zero(); right.columns()]; left.rows()];
    for (i, row) in rows.iter_mut().enumerate() {
        for (j, value) in row.iter_mut().enumerate() {
            for k in 0..left.columns() {
                *value += left.get(i, k)? * right.get(k, j)?;
            }
        }
    }
    Ok(Matrix::new(rows)?)
}

fn matrix_add(left: &Matrix, right: &Matrix) -> Result<Matrix> {
    if left.rows() != right.rows() || left.columns() != right.columns() {
        return Err("epoch matrix sum dimensions disagree".into());
    }
    let mut rows = left.to_rows();
    for i in 0..left.rows() {
        for j in 0..left.columns() {
            rows[i][j] += right.get(i, j)?;
        }
    }
    Ok(Matrix::new(rows)?)
}

fn matrix_subtract(left: &Matrix, right: &Matrix) -> Result<Matrix> {
    if left.rows() != right.rows() || left.columns() != right.columns() {
        return Err("epoch matrix difference dimensions disagree".into());
    }
    let mut rows = left.to_rows();
    for i in 0..left.rows() {
        for j in 0..left.columns() {
            rows[i][j] -= right.get(i, j)?;
        }
    }
    Ok(Matrix::new(rows)?)
}

fn released_gram_matrix(views: &[CutView], rows: usize, columns: usize) -> Result<Matrix> {
    released_gram_entries(
        views
            .iter()
            .flat_map(|view| view.gram_release.iter().cloned()),
        rows,
        columns,
    )
}

fn released_gram_entries(
    entries: impl IntoIterator<Item = (usize, Rat)>,
    rows: usize,
    columns: usize,
) -> Result<Matrix> {
    let entry_count = rows
        .checked_mul(columns)
        .ok_or("released Gram shape overflows usize")?;
    let mut values = Matrix::zero(rows, columns)?.to_rows();
    for (index, amount) in entries {
        if columns == 0 || index >= entry_count {
            return Err(
                format!("released Gram entry index {index} is outside {rows}x{columns}").into(),
            );
        }
        values[index / columns][index % columns] += amount;
    }
    Ok(Matrix::new(values)?)
}

fn prior_gram_delta(
    rows: usize,
    columns: usize,
    prior_cross: Option<u32>,
    prior_end: Option<u32>,
    scale_cross: u32,
    scale_end: u32,
) -> Result<Option<Matrix>> {
    if prior_cross != prior_end || (prior_cross.is_none() && scale_cross != scale_end) {
        return Ok(None);
    }
    let mut values = Matrix::zero(rows, columns)?.to_rows();
    if prior_cross.is_some() {
        if rows != columns {
            return Err("receiving prior ridge requires a square Gram matrix".into());
        }
        let ridge_cross = Rat::from_integer(BigInt::one() << scale_cross as usize);
        let ridge_end = Rat::from_integer(BigInt::one() << scale_end as usize);
        let delta = ridge_end - ridge_cross;
        for (i, row) in values.iter_mut().enumerate() {
            row[i] = delta.clone();
        }
    }
    Ok(Some(Matrix::new(values)?))
}

fn defer_conservation_verdict(
    failures: &mut Vec<String>,
    prior_delta_known: bool,
    adjusted_balance_zero: bool,
    adjusted_balance: &Matrix,
) {
    if !prior_delta_known {
        failures.push(
            "native Gram conservation is unsupported across an unaccounted prior declaration or scale change".into(),
        );
    } else if !adjusted_balance_zero {
        failures.push(format!(
            "native Gram conservation failed after exact prior adjustment: ΔHstored + Δcarry - ΔsampleH + released - Δprior = {}",
            matrix_summary(adjusted_balance)
        ));
    }
}

fn finish_deferred_failures(failures: Vec<String>) -> Result<()> {
    if failures.is_empty() {
        Ok(())
    } else {
        Err(failures.join("; ").into())
    }
}

fn column_majorizer(gram: &Matrix) -> Result<(Vec<i64>, Vec<Rat>)> {
    if !gram.is_square() {
        return Err("epoch metric is not square".into());
    }
    let mut exponents = Vec::with_capacity(gram.columns());
    let mut diagonal = Vec::with_capacity(gram.columns());
    for column in 0..gram.columns() {
        let mut norm = Rat::zero();
        for row in 0..gram.rows() {
            norm += gram.get(row, column)?.abs();
        }
        let exponent = ceil_log2_positive(&norm)
            .ok_or("column majorizer is undefined for a zero metric column")?;
        exponents.push(exponent);
        diagonal.push(rat_pow2(exponent));
    }
    Ok((exponents, diagonal))
}

fn right_column_scale(matrix: &Matrix, diagonal: &[Rat]) -> Result<Matrix> {
    if matrix.columns() != diagonal.len() {
        return Err("epoch diagonal scale width disagrees with matrix".into());
    }
    let mut rows = matrix.to_rows();
    for row in &mut rows {
        for (value, scale) in row.iter_mut().zip(diagonal) {
            *value /= scale;
        }
    }
    Ok(Matrix::new(rows)?)
}

fn project_toward_zero(matrix: &Matrix, lattice_exponent: u32) -> Result<Matrix> {
    let scale = rat_pow2(i64::from(lattice_exponent));
    let mut rows = matrix.to_rows();
    for row in &mut rows {
        for value in row {
            *value = Rat::from_integer((&*value * &scale).to_integer()) / &scale;
        }
    }
    Ok(Matrix::new(rows)?)
}

fn max_row_sum(matrix: &Matrix) -> Rat {
    (0..matrix.rows())
        .map(|row| {
            (0..matrix.columns()).fold(Rat::zero(), |sum, column| {
                sum + matrix
                    .get(row, column)
                    .map(Rat::abs)
                    .unwrap_or_else(|_| Rat::zero())
            })
        })
        .max()
        .unwrap_or_else(Rat::zero)
}

fn exact_fall(step: &Matrix, gradient: &Matrix, gram: &Matrix) -> Result<Rat> {
    let linear = step
        .entries()
        .iter()
        .zip(gradient.entries())
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b);
    let quadratic = matrix_product(&matrix_product(step, gram)?, &step.transpose()?)?;
    let trace = (0..quadratic.rows()).fold(Rat::zero(), |sum, i| {
        sum + quadratic.get(i, i).cloned().unwrap_or_else(|_| Rat::zero())
    });
    Ok(linear - trace / Rat::from_integer(BigInt::from(2)))
}

fn held_candidate_wave(
    frozen: &FrozenComparison,
    producing_map: &Matrix,
    candidate_map: &Matrix,
    samples: &[Sample],
) -> Result<Faces> {
    let wave = super::held_wave(candidate_map, producing_map, frozen.wave(), samples)?;
    // Exercise the same retained tree/phase combine path as recompare_covector/evaluate. The
    // combined value is not used to invent a parallel score; evaluate owns the exact objective.
    frozen.combined_faces(&wave)?;
    Ok(wave)
}

fn add_intervals(left: &mut Option<ExactInterval>, right: &ExactInterval) -> Result<()> {
    *left = Some(match left.take() {
        Some(total) => ExactInterval::new(total.lower + &right.lower, total.upper + &right.upper)?,
        None => right.clone(),
    });
    Ok(())
}

#[derive(Default)]
struct HeldOutputStats {
    record_bytes: usize,
    evaluated_record_bytes: usize,
    evaluated_records: usize,
}

fn held_readings_for_map(
    views: &[CutView],
    candidate_map: &Matrix,
    label: &str,
    branch: &str,
    total_samples: usize,
    budget: &mut timing::ReportBudget,
    held_eval_ns: &mut u128,
    output_stats: &mut HeldOutputStats,
) -> Result<()> {
    let mut before_total = None;
    let mut after_total = None;
    let mut change_total = None;
    let mut evaluated = 0usize;
    let mut unavailable = 0usize;
    let mut processed_cells = 0usize;
    let mut record_bytes = 0usize;
    let mut evaluated_record_bytes = 0usize;
    let mut cutoff_error = None;
    for (cell, view) in views.iter().enumerate() {
        let Some(frozen) = view.frozen.as_ref() else {
            let record = format!(
                "step0_epoch_held_reading branch={branch} cell={cell} candidate={label} status=unavailable reason=no-retained-frozen-comparison"
            );
            record_bytes = record_bytes.saturating_add(record.len());
            println!("{record}");
            unavailable += 1;
            processed_cells += 1;
            continue;
        };
        let work_label = format!("held comparison {label} cell {cell}");
        budget.check_before_work(&work_label)?;
        let started = Instant::now();
        let evaluation_result: Result<_> = (|| {
            let wave =
                held_candidate_wave(frozen, &view.producing_map, candidate_map, &view.samples)?;
            frozen.evaluate(&wave).map_err(Into::into)
        })();
        let elapsed_ns = started.elapsed().as_nanos();
        budget.record_work(timing::ReportWorkKind::HeldEval, elapsed_ns);
        *held_eval_ns = held_eval_ns.saturating_add(elapsed_ns);
        let reading = evaluation_result?;
        add_intervals(&mut before_total, &reading.before)?;
        add_intervals(&mut after_total, &reading.after)?;
        add_intervals(&mut change_total, &reading.objective_change)?;
        evaluated += 1;
        processed_cells += 1;
        let record = format!(
            "step0_epoch_held_reading branch={branch} cell={cell} candidate={label} before={:?} after={:?} objective_change={:?} unchanged={} strict_improvement={} needs_precision={} reason={}",
            reading.before,
            reading.after,
            reading.objective_change,
            reading.unchanged,
            reading.strictly_improved,
            reading.needs_precision(),
            reading.unresolved_reason()
        );
        record_bytes = record_bytes.saturating_add(record.len());
        evaluated_record_bytes = evaluated_record_bytes.saturating_add(record.len());
        println!("{record}");
        if budget.remaining_ns()? == 0 {
            cutoff_error = Some(format!(
                "branch {branch} crossed the shared report cutoff after retaining {work_label}"
            ));
            break;
        }
    }
    println!(
        "step0_epoch_held_objective_total branch={branch} candidate={label} evaluated_cells={evaluated} epoch_samples={total_samples} before={before_total:?} after={after_total:?} objective_change={change_total:?} metric=exact-sum-of-per-cell-frozen-comparison-intervals"
    );
    output_stats.record_bytes = output_stats.record_bytes.saturating_add(record_bytes);
    output_stats.evaluated_record_bytes = output_stats
        .evaluated_record_bytes
        .saturating_add(evaluated_record_bytes);
    output_stats.evaluated_records = output_stats.evaluated_records.saturating_add(evaluated);
    println!(
        "step0_epoch_held_output_bytes branch={branch} candidate={label} held_reading_record_bytes={record_bytes} held_reading_bytes_per_evaluated_cell={evaluated_record_bytes}/{evaluated} unavailable_records={unavailable} unprocessed_cells={} excludes_newlines_and_all_other_report_output=true",
        views.len().saturating_sub(processed_cells),
    );
    if let Some(error) = cutoff_error {
        return Err(error.into());
    }
    Ok(())
}

fn finish_report_budget(
    branch: &str,
    budget: &mut timing::ReportBudget,
    report_started: Instant,
    held_eval_ns: u128,
    inverse_ns: u128,
    output_stats: &HeldOutputStats,
) -> Option<String> {
    let total_ns = report_started.elapsed().as_nanos();
    let other_ns = total_ns.saturating_sub(held_eval_ns.saturating_add(inverse_ns));
    budget.record_work(timing::ReportWorkKind::Other, other_ns);
    let deadline_error = budget.check_before_work("epoch report completion").err();
    let summary = budget.finish();
    println!(
        "step0_epoch_report_projection branch={} held_eval_count={} held_eval_total_ns={} held_eval_max_ns={} gram_inverse_count={} gram_inverse_total_ns={} gram_inverse_max_ns={} other_count={} other_total_ns={} other_max_ns={} report_elapsed_ns={} projected_231_ns={:?} remaining_report_ns={} held_reading_record_bytes={} held_reading_bytes_per_evaluated_cell={}/{} excludes_newlines_and_all_other_report_output=true",
        summary.branch,
        summary.held_eval.count,
        summary.held_eval.total_ns,
        summary.held_eval.max_ns,
        summary.gram_inverse.count,
        summary.gram_inverse.total_ns,
        summary.gram_inverse.max_ns,
        summary.other.count,
        summary.other.total_ns,
        summary.other.max_ns,
        summary.elapsed_ns,
        summary.projected_231_ns,
        summary.remaining_report_ns,
        output_stats.record_bytes,
        output_stats.evaluated_record_bytes,
        output_stats.evaluated_records,
    );
    deadline_error.map(|error| {
        format!("branch {branch} completed its report readouts at the shared cutoff: {error}")
    })
}

/// Canonical exact-value identifier and the widths of the actual rational operands.
/// Other diagnostic records can use the same format without printing a complete matrix.
pub(super) fn matrix_summary(matrix: &Matrix) -> impl fmt::Display {
    exact_digest::matrix_summary(matrix)
}

fn stall_matrix(
    branch: &str,
    label: &str,
    matrix: &Matrix,
    budget: &timing::ReportBudget,
) -> Result<()> {
    let summary = exact_digest::matrix_summary_checked(matrix, || {
        budget.check_before_work("canonical exact matrix digest")
    })?;
    println!("step0_epoch_matrix branch={branch} operand={label} {summary}");
    budget.check_before_work("exact matrix digest output completion")?;
    Ok(())
}

fn stall_work<T>(
    budget: &timing::ReportBudget,
    label: &str,
    work: impl FnOnce() -> Result<T>,
) -> Result<T> {
    budget.check_before_work(label)?;
    let result = work();
    // A completed expensive kernel does not authorize the next one after the shared cutoff.
    budget.check_before_work(&format!("completion of {label}"))?;
    result
}

fn stall_product(left: &Matrix, right: &Matrix, budget: &timing::ReportBudget) -> Result<Matrix> {
    if left.columns() != right.rows() {
        return Err("stall matrix product dimensions disagree".into());
    }
    let mut rows = vec![vec![Rat::zero(); right.columns()]; left.rows()];
    for (i, row) in rows.iter_mut().enumerate() {
        for (j, value) in row.iter_mut().enumerate() {
            budget.check_before_work("exact stall product entry")?;
            for k in 0..left.columns() {
                *value += left.get(i, k)? * right.get(k, j)?;
            }
        }
    }
    budget.check_before_work("exact stall product completion")?;
    Ok(Matrix::shaped(left.rows(), right.columns(), rows)?)
}

/// Sylvester's criterion through successive exact Schur complements. The pivots are the ratios
/// of consecutive leading minors, so this retains the existing positive-definiteness condition
/// without recomputing every minor independently. This is a read of H', never a new native law.
fn positive_definite_with_check<E>(
    matrix: &Matrix,
    mut checkpoint: impl FnMut() -> std::result::Result<(), E>,
) -> std::result::Result<bool, E> {
    checkpoint()?;
    if !matrix_is_symmetric(matrix) {
        return Ok(false);
    }
    let mut values = matrix.to_rows();
    for pivot in 0..matrix.rows() {
        checkpoint()?;
        let diagonal = values[pivot][pivot].clone();
        if diagonal <= Rat::zero() {
            return Ok(false);
        }
        for row in pivot + 1..matrix.rows() {
            checkpoint()?;
            let factor = &values[row][pivot] / &diagonal;
            for column in row..matrix.columns() {
                let next = &values[row][column] - &factor * &values[pivot][column];
                values[row][column] = next.clone();
                values[column][row] = next;
            }
        }
    }
    checkpoint()?;
    Ok(true)
}

/// Full declared receiver-epoch stall read. It forms only the normal-law operands needed for
/// stalls and their witnesses; held-face candidate evaluations belong to the explicit profile.
/// G uses the native integer-statistics owner with explicit source-bound partition context,
/// and remains distinct from the inaccessible live PreparedStep.unit. No map from this read is deposited or certified.
pub(super) fn report_stall_epoch(
    branch: &str,
    crossing: &CutView,
    end: &CutView,
    views: &[CutView],
    receiver_grain: u64,
    budget: &mut timing::ReportBudget,
    capture: &mut ReportCapture,
) -> Result<()> {
    if receiver_grain == 0 {
        return Err("receiver grain denominator must be positive".into());
    }
    budget.check_before_work("stall epoch report")?;
    let report_started = Instant::now();
    let mut inverse_ns = 0;
    let mut deferred_failures = Vec::new();
    let readout = stall_epoch_readout(
        branch,
        crossing,
        end,
        views,
        receiver_grain,
        budget,
        capture,
        &mut inverse_ns,
        &mut deferred_failures,
    );
    if let Err(error) = readout {
        deferred_failures.push(error.to_string());
    }
    if let Some(error) = finish_report_budget(
        branch,
        budget,
        report_started,
        0,
        inverse_ns,
        &HeldOutputStats::default(),
    ) {
        deferred_failures.push(error);
    }
    finish_deferred_failures(deferred_failures)
}

#[allow(clippy::too_many_arguments)]
fn stall_epoch_readout(
    branch: &str,
    crossing: &CutView,
    end: &CutView,
    views: &[CutView],
    receiver_grain: u64,
    budget: &mut timing::ReportBudget,
    capture: &mut ReportCapture,
    inverse_ns: &mut u128,
    deferred_failures: &mut Vec<String>,
) -> Result<()> {
    let actual_b = amended_partition_receiver_exponent(receiver_grain)?;
    if require_partition_precision(crossing.receiver_partition_exponent)? != actual_b {
        return Err("compact stall report partition exponent disagrees with the native grain's amended half-cell conversion".into());
    }
    let (partitioned, exact_metric_scale) =
        stall_work(budget, "partitioned crossing statistics", || {
            partitioned_crossing_statistics(branch, crossing, views, budget)
        })?;
    let gradient = partitioned.gradient.clone();
    let sample_gram_delta = partitioned.gram_delta.clone();
    for (label, series) in [
        ("magnitude_positive_q_series", &partitioned.positive),
        ("magnitude_partitioned_foil_series", &partitioned.foil),
        ("whole_phase_series", &partitioned.phase),
    ] {
        stall_matrix(branch, label, series, budget)?;
    }
    for (sample, release) in partitioned.releases.iter().enumerate() {
        budget.check_before_work("exact partition release record")?;
        let integers = release
            .quotient
            .iter()
            .chain(&release.remainder)
            .chain(std::iter::once(&release.denominator))
            .cloned()
            .map(Rat::from_integer)
            .collect::<Vec<_>>();
        stall_matrix(
            branch,
            &format!("face_partition_integer_record_sample_{sample}"),
            &Matrix::new(vec![integers])?,
            budget,
        )?;
        println!(
            "step0_epoch_face_partition branch={branch} sample={sample} partition_exponent={} integer_record_order=quotients,remainder_numerators,normalizer classes={} exact_release_denominator=Z*2^L; retained_plus_release_equals_exact_face; remainder_not_added_to_G=true",
            partitioned.exponent,
            release.quotient.len()
        );
    }
    println!(
        "step0_epoch_partition_bound branch={branch} opening_native_receiver_ticks={:?} source_bound_epoch_index={:?} source_bound_cell_bound={:?} source_bound_receiver_exponent={:?} partition_exponent={} strict_released_magnitude_entry_bound={} phase_partition=none; bound_reported_separately_never_added",
        crossing.opening_crossings,
        crossing.partition_epoch_index,
        crossing.partition_cell_bound,
        crossing.receiver_partition_exponent,
        partitioned.exponent,
        partitioned.released_entry_bound
    );
    capture.gradient = Some(gradient.clone());
    capture.exact_metric_scale = exact_metric_scale.clone();
    let native_lw_cross = crossing.native_lattice_exponent;
    let native_lw_end = end.native_lattice_exponent;
    let spec_b_r = amended_partition_receiver_exponent(receiver_grain)?;
    let spec_lattice = specification_lattice_readout(
        receiver_grain,
        &crossing.support,
        crossing.map.columns(),
        native_lw_cross,
        native_lw_end,
    )?;
    let native_unit_cross = rat_pow2(-i64::from(native_lw_cross));
    let native_unit_end = rat_pow2(-i64::from(native_lw_end));
    let actual_map_delta = matrix_subtract(&end.map, &crossing.map)?;
    let actual_stored_gram_delta = matrix_subtract(&end.gram, &crossing.gram)?;
    let actual_carry_delta = matrix_subtract(&end.gram_remainder, &crossing.gram_remainder)?;
    let released_gram = released_gram_matrix(views, crossing.gram.rows(), crossing.gram.columns())?;
    let raw_gram_delta = matrix_subtract(
        &matrix_add(&actual_stored_gram_delta, &actual_carry_delta)?,
        &sample_gram_delta,
    )?;
    let raw_plus_release = matrix_add(&raw_gram_delta, &released_gram)?;
    let prior_delta = prior_gram_delta(
        crossing.gram.rows(),
        crossing.gram.columns(),
        crossing.receiving_prior,
        end.receiving_prior,
        crossing.prior_scale,
        end.prior_scale,
    )?;
    let adjusted_gram_balance = prior_delta
        .as_ref()
        .map(|prior| matrix_subtract(&raw_plus_release, prior))
        .transpose()?
        .unwrap_or_else(|| raw_plus_release.clone());
    let exact_gram_balance_zero = adjusted_gram_balance.entries().iter().all(Rat::is_zero);
    defer_conservation_verdict(
        deferred_failures,
        prior_delta.is_some(),
        exact_gram_balance_zero,
        &adjusted_gram_balance,
    );
    let conservation_status = if prior_delta.is_none() {
        "UNSUPPORTED-prior-change-or-scale-without-declared-prior"
    } else if exact_gram_balance_zero {
        "PASS-exact-zero"
    } else {
        "FAIL-nonzero-exact-balance"
    };
    let max_feature = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.feature)
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let max_live_g = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.covector)
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let max_sample_crossing_g = views
        .iter()
        .flat_map(|view| &view.crossing_covectors)
        .flatten()
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let newest_sample_weight = views
        .iter()
        .rev()
        .find_map(|view| view.samples.last())
        .map(|sample| &sample.weight);
    let zero_step_cells = views
        .iter()
        .filter(|view| view.receiving_step.is_zero())
        .count();
    let vanished_cells = views.iter().filter(|view| view.receiving_vanished).count();
    let grain_unit = Rat::new(BigInt::one(), BigInt::from(receiver_grain));
    let native_half_quantum = &grain_unit / Rat::from_integer(BigInt::from(2));

    for (label, matrix) in [
        ("W_cross", &crossing.map),
        ("H_cross_stored", &crossing.gram),
        ("G_cross_projected", &gradient),
        ("sample_H_delta_projected", &sample_gram_delta),
        ("H_prime_native_stored", &end.gram),
        ("H_stored_delta", &actual_stored_gram_delta),
        ("carry_cross", &crossing.gram_remainder),
        ("carry_end", &end.gram_remainder),
        ("carry_delta", &actual_carry_delta),
        ("raw_gram_delta", &raw_gram_delta),
        ("actual_sparse_released_gram", &released_gram),
        ("adjusted_conservation", &adjusted_gram_balance),
        ("W_end", &end.map),
        ("W_actual_delta", &actual_map_delta),
    ] {
        stall_matrix(branch, label, matrix, budget)?;
    }
    if let Some(prior) = &prior_delta {
        stall_matrix(branch, "exact_prior_delta", prior, budget)?;
    }
    let metric_scale_text = exact_metric_scale
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_else(|| "unavailable-native-unscaled-fallback".into());
    println!(
        "step0_epoch branch={branch} report=full-epoch-stalls samples={} cells={} exact_metric_scale_s={metric_scale_text} receiving_prior_cross={:?} receiving_prior_end={:?} prior_scale_cross={} prior_scale_end={} adjusted_conservation_exact_zero={exact_gram_balance_zero} conservation_status={conservation_status}",
        views.iter().map(|view| view.samples.len()).sum::<usize>(),
        views.len(),
        crossing.receiving_prior,
        end.receiving_prior,
        crossing.prior_scale,
        end.prior_scale,
    );
    println!(
        "step0_epoch_contract branch={branch} metric=native-stored-H; H_prime=H_end_stored; ridge_is_already_in_stored-H; gram_carry_reported_separately_not_added; G_cross=s*(positive_q_series-partitioned_foil_series)+whole_phase_series; native_class_metric_scale_or_explicit_unscaled_fallback; sample_deltaH_is_paired_projected; gamma=1_hypothetical; incoming_R=0_hypothetical; this_G_is_not_live_PreparedStep.unit; radial_mode=not_exposed; support_cross={:?} support_end={:?} symmetry_cross={} symmetry_end={} receiver_grain_unit=1/{receiver_grain}={grain_unit} native_precision_half_quantum={native_half_quantum}; no_candidate_map_or_held_face_pass",
        crossing.support, end.support, crossing.symmetry, end.symmetry,
    );
    let newest_weight = newest_sample_weight
        .map(ToString::to_string)
        .unwrap_or_else(|| "unavailable-no-staged-sample".into());
    println!(
        "step0_epoch_observables branch={branch} max_abs_f={max_feature} max_abs_live_sample_g={max_live_g} max_abs_input_crossing_g={max_sample_crossing_g} max_abs_G_cross_projected={} last_staged_sample_weight_as_newest_datum_weight={newest_weight} age-derived_nu_weight=not_exposed zero_step_cells={zero_step_cells} vanished_map_cells={vanished_cells} native_LW_cross={native_lw_cross} native_W_unit_cross={native_unit_cross} native_LW_end={native_lw_end} native_W_unit_end={native_unit_end} spec_b_R=ceil_log2(2*L_R)={spec_b_r:?} spec_LW_domain=explicit-solved-chart-support spec_LW_reading={spec_lattice:?} no_clock_feature_split_claimed",
        matrix_max_abs(&gradient),
    );

    let (majorizer_exponents, majorizer_diagonal) =
        stall_work(budget, "column majorizer", || column_majorizer(&end.gram))?;
    let d_hyp = stall_work(budget, "majorized direction D", || {
        right_column_scale(&gradient, &majorizer_diagonal)
    })?;
    let step = stall_work(budget, "crossing lattice projection Q(D)", || {
        project_toward_zero(&d_hyp, native_lw_cross)
    })?;
    let step_h = stall_product(&step, &end.gram, budget)?;
    let residual_after = stall_work(budget, "hypothetical R double prime", || {
        matrix_subtract(&gradient, &step_h)
    })?;
    // Read the quadratic fall directly as a Frobenius pairing; no rows-by-rows candidate
    // quadratic matrix is needed to read trace(Q H' Q^T).
    let linear = step
        .entries()
        .iter()
        .zip(gradient.entries())
        .fold(Rat::zero(), |sum, (q, g)| sum + q * g);
    let quadratic = step
        .entries()
        .iter()
        .zip(step_h.entries())
        .fold(Rat::zero(), |sum, (q, qh)| sum + q * qh);
    let fall = linear - quadratic / Rat::from_integer(BigInt::from(2));
    let nonzero_step = step.entries().iter().any(|value| !value.is_zero());
    let metric_pd = positive_definite_with_check(&end.gram, || {
        budget.check_before_work("exact positive-definiteness Schur complement")
    })?;
    let full_support = |support: &[usize], width: usize| {
        support.len() == width && support.iter().copied().eq(0..width)
    };
    let mut reasons = Vec::new();
    if !matrix_is_symmetric(&end.gram) {
        reasons.push("H_prime is not exactly symmetric");
    }
    if !metric_pd {
        reasons.push("H_prime positive-definiteness is not established");
    }
    if !full_support(&crossing.support, crossing.map.columns())
        || !full_support(&end.support, end.map.columns())
        || crossing.support != end.support
    {
        reasons.push("receiver chart support is not the same full declared coordinate set");
    }
    let gram_symmetry_ok = stall_work(budget, "native paired metric symmetry", || {
        Ok(
            gram_commutes_with_native_symmetry(&crossing.law, &crossing.gram)
                && gram_commutes_with_native_symmetry(&crossing.law, &crossing.gram_remainder)
                && gram_commutes_with_native_symmetry(&end.law, &end.gram)
                && gram_commutes_with_native_symmetry(&end.law, &end.gram_remainder)
                && gram_commutes_with_native_symmetry(&crossing.law, &sample_gram_delta)
                && gram_commutes_with_native_symmetry(&end.law, &sample_gram_delta),
        )
    })?;
    if !gram_symmetry_ok {
        reasons.push("stored Gram/carry/projected sample DeltaH does not commute with native paired symmetry");
    }
    let paired_operands_ok = stall_work(budget, "native paired direction and residual", || {
        let mut compatible = true;
        for operand in [&crossing.map, &gradient, &d_hyp, &step, &residual_after] {
            compatible &= map_respects_native_subspace(&crossing.law, operand)?
                && map_respects_native_subspace(&end.law, operand)?;
        }
        Ok(compatible)
    })?;
    if !paired_operands_ok {
        reasons.push("normal direction, step or residual leaves native paired subspace");
    }
    let fall_error = check_hypothetical_fall(nonzero_step, reasons.is_empty(), &fall).err();
    let fall_check = if !nonzero_step {
        "zero-step"
    } else if fall_error.is_some() {
        "FAIL"
    } else if reasons.is_empty() {
        "PASS"
    } else {
        "unconstrained-only"
    };
    if let Some(error) = fall_error {
        deferred_failures.push(error.to_string());
    }
    for (label, matrix) in [
        ("D_hyp", &d_hyp),
        ("Q_D_crossing_lattice", &step),
        ("R_double_prime_hyp", &residual_after),
    ] {
        stall_matrix(branch, label, matrix, budget)?;
    }
    println!(
        "step0_epoch_majorizer branch={branch} column_exponents={majorizer_exponents:?} M_diagonal_exact={} max_abs_D_hyp={} max_abs_D_in_crossing_W_units={} Q_D_exact_zero={} native_cross_fall={fall} positive_fall_check={fall_check} H_prime_positive_definite={metric_pd} gram_pair_symmetry_ok={gram_symmetry_ok} direction_step_residual_pair_subspace_ok={paired_operands_ok} constraints={reasons:?}; hypothetical_unconstrained_only; radial_constraint_certificate=not_exposed; no_live_deposit_refusal_claim",
        majorizer_diagonal
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(","),
        matrix_max_abs(&d_hyp),
        matrix_max_abs(&d_hyp) / &native_unit_cross,
        !nonzero_step,
    );

    budget.check_before_work("H prime exact inverse")?;
    let inverse_started = Instant::now();
    let inverse_result = end.gram.inverse();
    *inverse_ns = inverse_started.elapsed().as_nanos();
    budget.record_work(timing::ReportWorkKind::GramInverse, *inverse_ns);
    budget.check_before_work("H prime exact inverse completion")?;
    let inverse = match inverse_result {
        Ok(value) => value,
        Err(error) => {
            println!(
                "step0_epoch_stalls branch={branch} status=unavailable reason=singular-H_prime error={error}"
            );
            return Err(error.into());
        }
    };
    let unconstrained_update = stall_product(&gradient, &inverse, budget)?;
    let residual_dual = stall_product(&residual_after, &inverse, budget)?;
    for (label, matrix) in [
        ("H_prime_inverse", &inverse),
        ("R_prime_H_prime_inverse", &unconstrained_update),
        ("R_double_prime_H_prime_inverse", &residual_dual),
    ] {
        stall_matrix(branch, label, matrix, budget)?;
    }
    let mut stalled_entries = Vec::new();
    for row in 0..unconstrained_update.rows() {
        budget.check_before_work("stalled entries")?;
        for column in 0..unconstrained_update.columns() {
            let full = unconstrained_update.get(row, column)?.abs();
            let emitted = d_hyp.get(row, column)?.abs();
            if full >= native_unit_cross && emitted < native_unit_cross {
                stalled_entries.push((row, column));
                println!(
                    "step0_epoch_stalled_entry branch={branch} row={row} column={column} exact_abs_Rprime_Hprime_inverse={full} exact_abs_D={emitted} exact_Q_D={} native_W_unit_cross={native_unit_cross}",
                    step.get(row, column)?
                );
            }
        }
    }
    let witness_bound = max_row_sum(&residual_dual) * &max_feature;
    let width_bound = Rat::from_integer(BigInt::from(residual_dual.columns()))
        * matrix_max_abs(&residual_dual)
        * &max_feature;
    let mut max_witness = Rat::zero();
    let mut witnessed_rows = Vec::new();
    let mut witnesses_over_grain = 0usize;
    // A witness belongs to the residual row and sample, not to a duplicate column label.
    // Report each row/sample once, and keep every stalled coordinate in its own exact record.
    for &(row, _) in &stalled_entries {
        if witnessed_rows.contains(&row) {
            continue;
        }
        witnessed_rows.push(row);
        let mut row_max = Rat::zero();
        let mut row_witness = None;
        for (cell, view) in views.iter().enumerate() {
            budget.check_before_work("exact feature witnesses")?;
            for (sample_index, sample) in view.samples.iter().enumerate() {
                budget.check_before_work("exact feature witness sample")?;
                if sample.feature.len() != residual_dual.columns() {
                    return Err("stall witness feature width disagrees with residual dual".into());
                }
                let terms = sample
                    .feature
                    .iter()
                    .enumerate()
                    .map(|(j, f)| residual_dual.get(row, j).map(|dual| dual * f))
                    .collect::<std::result::Result<Vec<_>, _>>()?;
                let value: Rat = terms.iter().cloned().sum();
                let magnitude = value.abs();
                if magnitude >= grain_unit {
                    witnesses_over_grain += 1;
                    println!(
                        "step0_epoch_grain_witness branch={branch} row={row} cell={cell} sample={sample_index} exact_value={value} receiver_grain_q_R={grain_unit} verdict=AtOrAboveWholeGrain"
                    );
                }
                if row_witness.is_none() || magnitude > row_max {
                    row_max = magnitude;
                    row_witness = Some((cell, sample_index, value, terms));
                }
            }
        }
        if let Some((cell, sample_index, value, terms)) = row_witness {
            println!(
                "step0_epoch_max_row_witness branch={branch} row={row} cell={cell} sample={sample_index} exact_terms={} exact_sum={value} exact_abs={row_max} verdict={:?}",
                terms
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(","),
                silence_verdict(&row_max, &grain_unit)
            );
        }
        max_witness = max_witness.max(row_max);
    }
    budget.check_before_work("stall witness output completion")?;
    println!(
        "step0_epoch_stalls branch={branch} status={} stalled_entries={stalled_entries:?} count={} witnessed_rows={witnessed_rows:?} exact_max_feature_witness={max_witness} exact_witness_verdict={:?} norm_inf_Rdual_times_maxf_bound={witness_bound} norm_inf_silence_verdict={:?} width_times_max_entry_times_maxf_bound={width_bound} width_entry_silence_verdict={:?} unique_row_sample_witnesses_at_or_above_whole_grain={witnesses_over_grain} receiver_grain_q_R={grain_unit} native_half_quantum={native_half_quantum}; hypothetical_R_double_prime_only; no_live_deposit_refusal_claim",
        if reasons.is_empty() {
            "unconstrained-hypothetical"
        } else {
            "unconstrained-only-not-R12"
        },
        stalled_entries.len(),
        silence_verdict(&max_witness, &grain_unit),
        silence_verdict(&witness_bound, &grain_unit),
        silence_verdict(&width_bound, &grain_unit),
    );
    Ok(())
}

/// Report exact sample statistics and the explicitly hypothetical unit-gain normal-law step.
/// No data is deposited, no comparison is re-heard, and no result here substitutes for the
/// native per-step `PreparedStep.unit` or for a certified persistent residual.
pub(super) fn report_epoch(
    branch: &str,
    crossing: &CutView,
    end: &CutView,
    views: &[CutView],
    receiver_grain: u64,
    budget: &mut timing::ReportBudget,
    capture: &mut ReportCapture,
) -> Result<()> {
    if receiver_grain == 0 {
        return Err("receiver grain denominator must be positive".into());
    }
    budget.check_before_work("epoch report")?;
    let report_started = Instant::now();
    let mut held_eval_ns = 0u128;
    let mut inverse_ns = 0u128;
    let mut held_output_stats = HeldOutputStats::default();
    let (gradient, sample_gram_delta, exact_metric_scale) =
        super::epoch_statistics_with_scale(crossing, views)?;
    capture.gradient = Some(gradient.clone());
    capture.exact_metric_scale = exact_metric_scale.clone();
    let native_lw_cross = crossing.native_lattice_exponent;
    let native_lw_end = end.native_lattice_exponent;
    let spec_b_r = amended_partition_receiver_exponent(receiver_grain)?;
    let spec_lattice = specification_lattice_readout(
        receiver_grain,
        &crossing.support,
        crossing.map.columns(),
        native_lw_cross,
        native_lw_end,
    )?;
    let native_unit_cross = rat_pow2(-i64::from(native_lw_cross));
    let native_unit_end = rat_pow2(-i64::from(native_lw_end));
    let actual_map_delta = matrix_subtract(&end.map, &crossing.map)?;
    let actual_stored_gram_delta = matrix_subtract(&end.gram, &crossing.gram)?;
    let actual_carry_delta = matrix_subtract(&end.gram_remainder, &crossing.gram_remainder)?;
    let released_gram = released_gram_matrix(views, crossing.gram.rows(), crossing.gram.columns())?;
    let raw_gram_delta = matrix_subtract(
        &matrix_add(&actual_stored_gram_delta, &actual_carry_delta)?,
        &sample_gram_delta,
    )?;
    let raw_plus_release = matrix_add(&raw_gram_delta, &released_gram)?;
    let prior_delta = prior_gram_delta(
        crossing.gram.rows(),
        crossing.gram.columns(),
        crossing.receiving_prior,
        end.receiving_prior,
        crossing.prior_scale,
        end.prior_scale,
    )?;
    let adjusted_gram_balance = prior_delta
        .as_ref()
        .map(|prior| matrix_subtract(&raw_plus_release, prior))
        .transpose()?
        .unwrap_or_else(|| raw_plus_release.clone());
    let exact_gram_balance_zero = adjusted_gram_balance.entries().iter().all(Rat::is_zero);
    let mut deferred_failures = Vec::new();
    defer_conservation_verdict(
        &mut deferred_failures,
        prior_delta.is_some(),
        exact_gram_balance_zero,
        &adjusted_gram_balance,
    );
    let conservation_status = if prior_delta.is_none() {
        "UNSUPPORTED-prior-change-or-scale-without-declared-prior"
    } else if exact_gram_balance_zero {
        "PASS-exact-zero"
    } else {
        "FAIL-nonzero-exact-balance"
    };
    let max_feature = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.feature)
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let max_live_g = views
        .iter()
        .flat_map(|view| &view.samples)
        .flat_map(|sample| &sample.covector)
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let max_sample_crossing_g = views
        .iter()
        .flat_map(|view| &view.crossing_covectors)
        .flatten()
        .map(Rat::abs)
        .max()
        .unwrap_or_else(Rat::zero);
    let newest_sample_weight = views
        .iter()
        .rev()
        .find_map(|view| view.samples.last())
        .map(|sample| &sample.weight);
    let zero_step_cells = views
        .iter()
        .filter(|view| view.receiving_step.is_zero())
        .count();
    let vanished_cells = views.iter().filter(|view| view.receiving_vanished).count();
    let grain_unit = Rat::new(BigInt::one(), BigInt::from(receiver_grain));
    let native_half_quantum = &grain_unit / Rat::from_integer(BigInt::from(2));

    println!(
        "step0_epoch branch={branch} samples={} W_cross={:?} H_cross_stored={:?} G_cross_projected={:?} exact_metric_scale_s={exact_metric_scale:?} sample_H_delta_projected={:?} H_end_stored={:?} H_stored_delta={:?} carry_cross={:?} carry_end={:?} carry_delta={:?} raw_ΔHstored_plus_Δcarry_minus_ΔsampleH={:?} actual_sparse_released_gram_e={:?} exact_ΔP_prior={:?} adjusted_conservation_raw_plus_e_minus_ΔP={:?} adjusted_conservation_exact_zero={} receiving_prior_cross={:?} receiving_prior_end={:?} prior_scale_cross={} prior_scale_end={} conservation_status={}; when exact ΔP is unavailable no conservation claim is made W_end={:?} W_actual_delta={:?}",
        views.iter().map(|view| view.samples.len()).sum::<usize>(),
        crossing.map,
        crossing.gram,
        gradient,
        sample_gram_delta,
        end.gram,
        actual_stored_gram_delta,
        crossing.gram_remainder,
        end.gram_remainder,
        actual_carry_delta,
        raw_gram_delta,
        released_gram,
        &prior_delta,
        adjusted_gram_balance,
        exact_gram_balance_zero,
        crossing.receiving_prior,
        end.receiving_prior,
        crossing.prior_scale,
        end.prior_scale,
        conservation_status,
        end.map,
        actual_map_delta,
    );
    println!(
        "step0_epoch_contract branch={branch} metric=native-stored-H; ridge_is_already_in_stored-H; gram_carry_reported_separately_not_added; G_cross_uses_native_receiving_metric_samples_when_scale_s_is_Some_and_unscaled_fallback_when_None; sample_deltaH_is_paired_projected; gamma=1_hypothetical; incoming_R=0_hypothetical; this_G_is_not_live_PreparedStep.unit; radial_mode=not_exposed; receiving_prior={:?} prior_scale={} support={:?} symmetry={} receiver_grain_unit=1/{receiver_grain}={grain_unit} native_precision_half_quantum={native_half_quantum}",
        crossing.receiving_prior, crossing.prior_scale, crossing.support, crossing.symmetry,
    );
    println!(
        "step0_epoch_observables branch={branch} max_abs_f={max_feature} max_abs_live_sample_g={max_live_g} max_abs_input_crossing_g={max_sample_crossing_g} max_abs_G_cross_projected={} last_staged_sample_weight_as_newest_datum_weight={newest_sample_weight:?} age-derived_nu_weight=not_exposed zero_step_cells={zero_step_cells} vanished_map_cells={vanished_cells} native_LW_cross={native_lw_cross} native_W_unit_cross={native_unit_cross} native_LW_end={native_lw_end} native_W_unit_end={native_unit_end} spec_b_R=ceil_log2(2*L_R)={spec_b_r:?} spec_LW_domain=explicit-solved-chart-support spec_LW_reading={spec_lattice:?} no_clock_feature_split_claimed",
        matrix_max_abs(&gradient),
    );

    // This is the stated step-0 hypothetical law: no persistent native carry is present in the
    // captured API, so R' is exactly the unit-gain crossing gradient for this readout only.
    let residual_prime = gradient.clone();
    let majorizer_result = column_majorizer(&end.gram);
    let (majorizer_exponents, majorizer_diagonal) = match majorizer_result {
        Ok(value) => value,
        Err(error) => {
            println!(
                "step0_epoch_candidate branch={branch} status=unavailable reason={error}; zero-or-invalid-column-majorizer"
            );
            let sample_count = views.iter().map(|view| view.samples.len()).sum();
            held_readings_for_map(
                views,
                &crossing.map,
                "W_cross",
                branch,
                sample_count,
                budget,
                &mut held_eval_ns,
                &mut held_output_stats,
            )?;
            held_readings_for_map(
                views,
                &end.map,
                "W_end",
                branch,
                sample_count,
                budget,
                &mut held_eval_ns,
                &mut held_output_stats,
            )?;
            if let Some(error) = finish_report_budget(
                branch,
                budget,
                report_started,
                held_eval_ns,
                inverse_ns,
                &held_output_stats,
            ) {
                deferred_failures.push(error);
            }
            return finish_deferred_failures(deferred_failures);
        }
    };
    let d_hyp = right_column_scale(&residual_prime, &majorizer_diagonal)?;
    let lattice_unit = native_unit_cross.clone();
    let step = project_toward_zero(&d_hyp, native_lw_cross)?;
    let end_lattice_step = project_toward_zero(&d_hyp, native_lw_end)?;
    let candidate_map = matrix_add(&crossing.map, &step)?;
    let residual_after = matrix_subtract(&residual_prime, &matrix_product(&step, &end.gram)?)?;
    let end_lattice_residual = matrix_subtract(
        &residual_prime,
        &matrix_product(&end_lattice_step, &end.gram)?,
    )?;
    let fall = exact_fall(&step, &residual_prime, &end.gram)?;
    let end_lattice_fall = exact_fall(&end_lattice_step, &residual_prime, &end.gram)?;
    budget.check_before_work("end Gram inverse")?;
    let inverse_started = Instant::now();
    let inverse_result = end.gram.inverse();
    inverse_ns = inverse_started.elapsed().as_nanos();
    budget.record_work(timing::ReportWorkKind::GramInverse, inverse_ns);
    if budget.remaining_ns()? == 0 {
        return Err(format!(
            "branch {branch} crossed the shared report cutoff while computing the end Gram inverse"
        )
        .into());
    }
    let inverse = match inverse_result {
        Ok(inverse) => inverse,
        Err(error) => {
            println!(
                "step0_epoch_stalls branch={branch} status=unavailable reason=singular-H_end error={error}"
            );
            let sample_count = views.iter().map(|view| view.samples.len()).sum();
            held_readings_for_map(
                views,
                &crossing.map,
                "W_cross",
                branch,
                sample_count,
                budget,
                &mut held_eval_ns,
                &mut held_output_stats,
            )?;
            held_readings_for_map(
                views,
                &end.map,
                "W_end",
                branch,
                sample_count,
                budget,
                &mut held_eval_ns,
                &mut held_output_stats,
            )?;
            if let Some(error) = finish_report_budget(
                branch,
                budget,
                report_started,
                held_eval_ns,
                inverse_ns,
                &held_output_stats,
            ) {
                deferred_failures.push(error);
            }
            return finish_deferred_failures(deferred_failures);
        }
    };
    let unconstrained_update = matrix_product(&residual_prime, &inverse)?;
    let optimum = matrix_add(&crossing.map, &unconstrained_update)?;
    let mut unconstrained_reasons = unconstrained_reasons(
        &crossing.support,
        crossing.map.columns(),
        &end.support,
        end.map.columns(),
        &end.gram,
    );
    if !gram_commutes_with_native_symmetry(&crossing.law, &crossing.gram)
        || !gram_commutes_with_native_symmetry(&crossing.law, &crossing.gram_remainder)
        || !gram_commutes_with_native_symmetry(&end.law, &end.gram)
        || !gram_commutes_with_native_symmetry(&end.law, &end.gram_remainder)
        || !gram_commutes_with_native_symmetry(&crossing.law, &sample_gram_delta)
        || !gram_commutes_with_native_symmetry(&end.law, &sample_gram_delta)
    {
        unconstrained_reasons.push("stored Gram/carry/projected sample DeltaH does not commute with native paired symmetry");
    }
    let cross_step_compatible = map_respects_native_subspace(&crossing.law, &step)?
        && map_respects_native_subspace(&end.law, &step)?
        && map_respects_native_subspace(&crossing.law, &end_lattice_step)?
        && map_respects_native_subspace(&end.law, &end_lattice_step)?
        && map_respects_native_subspace(&crossing.law, &residual_after)?
        && map_respects_native_subspace(&end.law, &residual_after)?;
    let cross_candidate_compatible = map_respects_native_subspace(&crossing.law, &candidate_map)?
        && map_respects_native_subspace(&end.law, &candidate_map)?;
    let end_candidate_compatible = map_respects_native_subspace(&crossing.law, &optimum)?
        && map_respects_native_subspace(&end.law, &optimum)?;
    if !cross_step_compatible || !cross_candidate_compatible || !end_candidate_compatible {
        unconstrained_reasons.push("projected step or candidate map leaves native paired subspace");
    }
    let nonzero_step = !step.entries().iter().all(Rat::is_zero);
    let fall_error =
        check_hypothetical_fall(nonzero_step, unconstrained_reasons.is_empty(), &fall).err();
    let fall_defect = fall_error.is_some();
    let fall_check = if !nonzero_step {
        "zero-step"
    } else if unconstrained_reasons.is_empty() && !fall_defect {
        "PASS"
    } else if fall_defect {
        "FAIL"
    } else {
        "unconstrained-only"
    };
    let actual_end_gap = matrix_subtract(&end.map, &optimum)?;
    println!(
        "step0_epoch_majorizer branch={branch} column_exponents={majorizer_exponents:?} M_diagonal={majorizer_diagonal:?} D_hyp={d_hyp:?} max_abs_D_hyp={} max_abs_D_in_crossing_W_units={} native_LW_cross={native_lw_cross} native_LW_end={native_lw_end} native_cross_step={step:?} native_cross_R_double_prime={residual_after:?} native_cross_fall={fall} native_end_step_diagnostic={end_lattice_step:?} native_end_R_double_prime_diagnostic={end_lattice_residual:?} native_end_fall_diagnostic={end_lattice_fall} positive_fall_check={fall_check} step_pair_subspace_ok={cross_step_compatible} native_cross_candidate_pair_subspace_ok={cross_candidate_compatible} W_star_pair_subspace_ok={end_candidate_compatible} actual_W_end_minus_W_star_unconstrained={actual_end_gap:?}",
        matrix_max_abs(&d_hyp),
        matrix_max_abs(&d_hyp) / &lattice_unit,
    );
    println!(
        "step0_epoch_quadratic_candidate branch={branch} status={} W_star_unconstrained={optimum:?} exact_normal_residual=0 objective=unconstrained_exact_prox_quadratic_only; radial_constraint_certificate=not_exposed; frozen-comparison-readings-are-reported-separately; not_a_certified_native_update; W_end_gap_is_not_a_deposit_law_defect constraints={unconstrained_reasons:?}",
        if unconstrained_reasons.is_empty() && (fall_check == "PASS" || fall_check == "zero-step") {
            "exact-unconstrained-diagnostic"
        } else {
            "not-admitted-as-lawful-candidate"
        }
    );
    let residual_dual = matrix_product(&residual_after, &inverse)?;
    let mut stalls = Vec::new();
    for i in 0..unconstrained_update.rows() {
        for j in 0..unconstrained_update.columns() {
            let full = unconstrained_update.get(i, j)?.abs();
            let emitted = d_hyp.get(i, j)?.abs();
            if full >= lattice_unit && emitted < lattice_unit {
                stalls.push((i, j));
            }
        }
    }
    let witness_bound = max_row_sum(&residual_dual) * &max_feature;
    let width_times_entry_bound = Rat::from_integer(BigInt::from(residual_dual.columns()))
        * matrix_max_abs(&residual_dual)
        * &max_feature;
    let mut witnesses_over_grain = Vec::new();
    let mut max_witness = Rat::zero();
    for &(row, column) in &stalls {
        for (cell, view) in views.iter().enumerate() {
            for (sample_index, sample) in view.samples.iter().enumerate() {
                if sample.feature.len() != residual_dual.columns() {
                    return Err("stall witness feature width disagrees with residual dual".into());
                }
                let value = (0..sample.feature.len()).fold(Rat::zero(), |sum, j| {
                    sum + residual_dual
                        .get(row, j)
                        .cloned()
                        .unwrap_or_else(|_| Rat::zero())
                        * &sample.feature[j]
                });
                let magnitude = value.abs();
                if magnitude >= grain_unit {
                    witnesses_over_grain.push((row, column, cell, sample_index, value));
                }
                max_witness = max_witness.max(magnitude);
            }
        }
    }
    let exact_witness_verdict = silence_verdict(&max_witness, &grain_unit);
    let norm_inf_bound_verdict = silence_verdict(&witness_bound, &grain_unit);
    let width_entry_bound_verdict = silence_verdict(&width_times_entry_bound, &grain_unit);
    println!(
        "step0_epoch_stalls branch={branch} status={} stalled_entries={stalls:?} count={} exact_max_feature_witness={max_witness} exact_witness_verdict={exact_witness_verdict:?} norm_inf_Rdual_times_maxf_bound={witness_bound} norm_inf_silence_verdict={norm_inf_bound_verdict:?} width_times_max_entry_times_maxf_bound={width_times_entry_bound} width_entry_silence_verdict={width_entry_bound_verdict:?} per_feature_witnesses_at_or_above_whole_grain={witnesses_over_grain:?} receiver_grain_q_R={grain_unit} native_half_quantum={native_half_quantum}; hypothetical_R_double_prime_only; no_live_deposit_refusal_claim",
        if unconstrained_reasons.is_empty() {
            "unconstrained-hypothetical"
        } else {
            "unconstrained-only-not-R12"
        },
        stalls.len(),
    );

    let sample_count = views.iter().map(|view| view.samples.len()).sum();
    held_readings_for_map(
        views,
        &crossing.map,
        "W_cross",
        branch,
        sample_count,
        budget,
        &mut held_eval_ns,
        &mut held_output_stats,
    )?;
    held_readings_for_map(
        views,
        &end.map,
        "W_end",
        branch,
        sample_count,
        budget,
        &mut held_eval_ns,
        &mut held_output_stats,
    )?;
    held_readings_for_map(
        views,
        &optimum,
        "W_star_unconstrained",
        branch,
        sample_count,
        budget,
        &mut held_eval_ns,
        &mut held_output_stats,
    )?;
    if let Some(error) = fall_error {
        deferred_failures.push(error.to_string());
    }
    if let Some(error) = finish_report_budget(
        branch,
        budget,
        report_started,
        held_eval_ns,
        inverse_ns,
        &held_output_stats,
    ) {
        deferred_failures.push(error);
    }
    finish_deferred_failures(deferred_failures)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn matrix(rows: &[&[i64]]) -> Matrix {
        Matrix::new(
            rows.iter()
                .map(|row| row.iter().map(|x| Rat::from_integer((*x).into())).collect())
                .collect(),
        )
        .unwrap()
    }

    fn clock_binding_declaration() -> holonics::hnn::FieldDeclaration {
        let mut declared = holonics::hnn::FieldDeclaration::campaign_one(1 << 17);
        declared.rings.truncate(3);
        declared
            .contacts
            .retain(|contact| contact.from < 3 && contact.to < 3);
        declared.loops.clear();
        declared.sources = vec![0];
        declared.rings[0].lock = (0..declared.alphabet as u64).collect();
        declared.rings[1].lock.clear();
        declared.rings[2].lock.clear();
        declared.receivers[0].ring = 2;
        declared.receivers[0].aperture = 1;
        declared
    }

    #[test]
    fn receiver_clock_binding_uses_actual_ticks_and_distinguishes_full_winding() {
        let field = Field::declare(clock_binding_declaration().by_lattice_rule()).unwrap();
        let (_, bound) = opening_partition_context(&field, Some(0)).unwrap();
        assert_eq!(bound, 5 * 7);
        let terrain = holonics::holarchy::terrain::KnownTruth::uniform(
            field.alphabet(),
            0,
            1,
            (2 * bound) as usize,
        )
        .unwrap();
        let word = holonics::hnn::Encoded::identity(&terrain, &field)
            .unwrap()
            .remove(0);
        let mut current = holonics::hnn::Current::at_rest(&field);
        let mut ticks = 0u64;
        for at in 0..word.len() {
            let step = current.step(&field, &word, at).unwrap();
            ticks += step.ticks[2];
            let (c, k) = opening_partition_context(&field, Some(ticks)).unwrap();
            assert_eq!(k, bound);
            assert_eq!(c, ((at + 1) as u64) / bound);
        }
        assert_eq!(ticks, 2);
        assert_eq!(current.winding(&field, 2).unwrap(), BigInt::zero());
        // A recorded count is not reconstructed from any supplied source length or lift phase.
        assert_eq!(
            opening_partition_context(&field, Some(17)).unwrap(),
            (17, bound)
        );
        assert!(opening_partition_context(&field, None).is_err());
    }

    #[test]
    fn receiver_clock_binding_refuses_nonuniform_locks_and_other_receivers() {
        let mut declared = clock_binding_declaration();
        declared.rings[0].lock.pop();
        let field = Field::declare(declared.by_lattice_rule()).unwrap();
        assert!(opening_partition_context(&field, Some(0)).is_err());
        let mut declared = clock_binding_declaration();
        declared.rings[1].lock = vec![0];
        let field = Field::declare(declared.by_lattice_rule()).unwrap();
        assert!(opening_partition_context(&field, Some(0)).is_err());
        let mut declared = clock_binding_declaration();
        declared.receivers[0].aperture = 2;
        let field = Field::declare(declared.by_lattice_rule()).unwrap();
        assert!(opening_partition_context(&field, Some(0)).is_err());
        assert!(receiver_partition_cell_bound(u64::MAX, 2).is_err());
        assert!(receiver_partition_cell_bound(1, 7).is_err());
    }

    #[test]
    fn amended_partition_exponent_is_exact_ceil_of_the_native_half_cell() {
        assert!(amended_partition_receiver_exponent(0).is_err());
        for (grain, expected) in [
            (1, 1),
            (2, 2),
            (3, 3),
            (31, 6),
            (32, 6),
            (33, 7),
            (u64::MAX / 2, 64),
            (u64::MAX, 65),
        ] {
            let b = amended_partition_receiver_exponent(grain).unwrap();
            assert_eq!(b, expected);
            let doubled = u128::from(grain) * 2;
            assert!(doubled <= (1u128 << b));
            assert!((1u128 << (b - 1)) < doubled);
        }
        // The partition is at or finer than half a cell, including a non-dyadic cell.
        let b = amended_partition_receiver_exponent(3).unwrap();
        assert!(rat_pow2(-i64::from(b)) <= Rat::new(1.into(), 6.into()));
        assert_eq!(amended_partition_receiver_exponent(32).unwrap(), 6);
    }

    #[test]
    fn amended_native_partition_schedule_matches_the_owner_crossings() {
        let context = PartitionContext {
            receiver_exponent: amended_partition_receiver_exponent(32).unwrap(),
            cell_bound: 231,
            epoch_index: 0,
            phase_period: 11,
        };
        for (c, expected) in [
            (0, 15),
            (1, 17),
            (2, 19),
            (3, 19),
            (4, 21),
            (5, 21),
            (6, 21),
            (7, 21),
            (8, 23),
        ] {
            assert_eq!(
                partition_exponent_explicit(PartitionContext {
                    epoch_index: c,
                    ..context
                })
                .unwrap(),
                expected
            );
        }
        assert_eq!(
            rat_pow2(-i64::from(context.receiver_exponent)),
            Rat::new(1.into(), 64.into())
        );
        assert_ne!(context.receiver_exponent, 32);
    }

    #[test]
    fn partition_precision_and_epoch_clock_are_explicit_operands() {
        assert!(
            require_partition_precision(None)
                .unwrap_err()
                .to_string()
                .contains("denominator is not an exponent")
        );
        assert_eq!(require_partition_precision(Some(32)).unwrap(), 32);
        let context = PartitionContext {
            receiver_exponent: 32,
            cell_bound: 231,
            epoch_index: 0,
            phase_period: 11,
        };
        assert_eq!(partition_exponent_explicit(context).unwrap(), 41);
        assert_eq!(
            partition_exponent_explicit(PartitionContext {
                epoch_index: 704_776,
                ..context
            })
            .unwrap(),
            81
        );
        assert!(
            partition_exponent_explicit(PartitionContext {
                cell_bound: 0,
                ..context
            })
            .is_err()
        );
        assert!(
            partition_exponent_explicit(PartitionContext {
                epoch_index: u64::MAX,
                ..context
            })
            .is_err()
        );
    }

    #[test]
    fn partitioned_integer_series_keep_release_and_whole_phase_separate() {
        let law = NormalLaw::with_prior(Matrix::zero(4, 2).unwrap());
        let samples = [PartitionSample {
            feature: vec![Rat::new(1.into(), 2.into()), -Rat::one()],
            weights: vec![1.into(), 2.into()],
            normalizer: 3.into(),
            target: 0,
            phase: vec![Rat::new(1.into(), 22.into()), Rat::zero()],
        }];
        let context = PartitionContext {
            receiver_exponent: 0,
            cell_bound: 1,
            epoch_index: 0,
            phase_period: 11,
        };
        let scale = Rat::from_integer(2.into());
        let stats =
            partitioned_statistics(&law, &samples, context, Some(&scale), || Ok(())).unwrap();
        assert_eq!(stats.exponent, 1);
        assert_eq!(stats.releases[0].quotient, vec![0.into(), 1.into()]);
        assert_eq!(stats.releases[0].remainder, vec![2.into(), 1.into()]);
        for class in 0..2 {
            assert_eq!(
                &samples[0].weights[class] << stats.exponent as usize,
                &stats.releases[0].quotient[class] * &stats.releases[0].denominator
                    + &stats.releases[0].remainder[class]
            );
            assert!(stats.releases[0].remainder[class] >= BigInt::zero());
            assert!(stats.releases[0].remainder[class] < stats.releases[0].denominator);
        }
        assert_eq!(stats.gradient.get(0, 0).unwrap(), &Rat::one());
        assert_eq!(
            stats.gradient.get(0, 1).unwrap(),
            &Rat::from_integer((-2).into())
        );
        assert_eq!(
            stats.gradient.get(2, 0).unwrap(),
            &Rat::new((-1).into(), 2.into())
        );
        assert_eq!(
            stats.gradient.get(1, 0).unwrap(),
            &Rat::new(1.into(), 44.into())
        );
        assert_eq!(
            stats.phase.get(1, 0).unwrap(),
            stats.gradient.get(1, 0).unwrap()
        );
        assert_eq!(stats.released_entry_bound, Rat::one());
        // The release stays separate from the retained gradient.
        assert_ne!(
            stats.gradient.get(0, 0).unwrap(),
            &Rat::new(2.into(), 3.into())
        );
        assert_eq!(
            stats.gram_delta.get(0, 0).unwrap(),
            &Rat::new(1.into(), 4.into())
        );
    }

    #[test]
    fn partition_rejects_foreign_features_phase_factors_and_expired_work() {
        let law = NormalLaw::with_prior(Matrix::zero(4, 1).unwrap());
        let context = PartitionContext {
            receiver_exponent: 3,
            cell_bound: 1,
            epoch_index: 0,
            phase_period: 11,
        };
        let phase_foreign = PartitionSample {
            feature: vec![Rat::one()],
            weights: vec![1.into(), 2.into()],
            normalizer: 3.into(),
            target: 0,
            phase: vec![Rat::new(1.into(), 3.into()), Rat::zero()],
        };
        assert!(partitioned_statistics(&law, &[phase_foreign], context, None, || Ok(())).is_err());
        let feature_foreign = PartitionSample {
            feature: vec![Rat::new(1.into(), 3.into())],
            weights: vec![1.into(), 2.into()],
            normalizer: 3.into(),
            target: 0,
            phase: vec![Rat::zero(); 2],
        };
        assert!(
            partitioned_statistics(&law, &[feature_foreign], context, None, || Ok(())).is_err()
        );
        let result =
            partitioned_statistics(&law, &[], context, None, || Err("shared-cutoff".into()));
        assert!(result.err().unwrap().to_string().contains("shared-cutoff"));
    }

    #[test]
    fn receiving_sample_bound_reads_actual_population_and_rejects_multiplicity() {
        assert_eq!(checked_heard_sample_population(&[0, 1, 1], 231).unwrap(), 2);
        assert_eq!(
            checked_heard_sample_population(&[1; 231], 231).unwrap(),
            231
        );
        assert!(checked_heard_sample_population(&[1; 232], 231).is_err());
        assert!(checked_heard_sample_population(&[2], 231).is_err());
        assert!(checked_heard_sample_population(&[], 0).is_err());
    }

    #[test]
    fn partition_count_and_phase_period_refusals_name_the_actual_operand() {
        let law = NormalLaw::with_prior(Matrix::zero(4, 1).unwrap());
        let context = PartitionContext {
            receiver_exponent: 6,
            cell_bound: 1,
            epoch_index: 0,
            phase_period: 11,
        };
        let sample = || PartitionSample {
            feature: vec![Rat::one()],
            weights: vec![1.into(), 2.into()],
            normalizer: 3.into(),
            target: 0,
            phase: vec![Rat::zero(); 2],
        };
        let excess = partitioned_statistics(&law, &[sample(), sample()], context, None, || Ok(()));
        assert!(
            excess
                .err()
                .unwrap()
                .to_string()
                .contains("actual partition sample count")
        );
        let bad_period = partition_exponent_explicit(PartitionContext {
            phase_period: 0,
            ..context
        });
        assert!(
            bad_period
                .err()
                .unwrap()
                .to_string()
                .contains("receiving phase period")
        );
        let bad_bound = partition_exponent_explicit(PartitionContext {
            cell_bound: 0,
            ..context
        });
        assert!(
            bad_bound
                .err()
                .unwrap()
                .to_string()
                .contains("heard-sample bound")
        );
    }

    #[test]
    fn hypothetical_majorizer_projection_and_fall_are_exact() {
        let h = matrix(&[&[2, 0], &[0, 4]]);
        let g = matrix(&[&[3, -1], &[1, 2]]);
        let (exponents, m) = column_majorizer(&h).unwrap();
        assert_eq!(exponents, vec![1, 2]);
        assert_eq!(
            m,
            vec![Rat::from_integer(2.into()), Rat::from_integer(4.into())]
        );
        let d = right_column_scale(&g, &m).unwrap();
        assert_eq!(
            d,
            Matrix::new(vec![
                vec![
                    Rat::new(3.into(), 2.into()),
                    Rat::new((-1).into(), 4.into())
                ],
                vec![Rat::new(1.into(), 2.into()), Rat::new(1.into(), 2.into())],
            ])
            .unwrap()
        );
        let step = project_toward_zero(&d, 0).unwrap();
        assert_eq!(step, matrix(&[&[1, 0], &[0, 0]]));
        let residual = matrix_subtract(&g, &matrix_product(&step, &h).unwrap()).unwrap();
        assert_eq!(residual, matrix(&[&[1, -1], &[1, 2]]));
        assert_eq!(
            exact_fall(&step, &g, &h).unwrap(),
            Rat::from_integer(2.into())
        );
    }

    #[test]
    fn exact_schur_read_preserves_sylvester_condition_and_cutoff() {
        for h in [
            matrix(&[&[2, 1], &[1, 2]]),
            matrix(&[&[1, 2], &[2, 1]]),
            matrix(&[&[1, 1], &[1, 1]]),
            matrix(&[&[2, 1], &[0, 2]]),
            matrix(&[&[4, 1, 1], &[1, 3, 1], &[1, 1, 2]]),
        ] {
            assert_eq!(
                positive_definite_with_check(&h, || Ok::<_, &str>(())).unwrap(),
                is_positive_definite(&h)
            );
        }
        let mut checks = 0;
        let result = positive_definite_with_check(&matrix(&[&[2, 1], &[1, 2]]), || {
            checks += 1;
            if checks == 3 {
                Err("shared-cutoff")
            } else {
                Ok(())
            }
        });
        assert_eq!(result, Err("shared-cutoff"));
    }

    #[test]
    fn zero_majorized_projection_can_stall_with_exact_whole_grain_witness() {
        // The off-diagonal metric cancels on this row: the full normal direction is (1,-1),
        // while the absolute-column majorizer returns (1/4,-1/4), below the native unit.
        let h = matrix(&[&[2, 1], &[1, 2]]);
        let g = matrix(&[&[1, -1]]);
        let (_, majorizer) = column_majorizer(&h).unwrap();
        let d = right_column_scale(&g, &majorizer).unwrap();
        let q = project_toward_zero(&d, 0).unwrap();
        assert_eq!(q, Matrix::zero(1, 2).unwrap());
        let residual = matrix_subtract(&g, &matrix_product(&q, &h).unwrap()).unwrap();
        let full = matrix_product(&g, &h.inverse().unwrap()).unwrap();
        let dual = matrix_product(&residual, &h.inverse().unwrap()).unwrap();
        assert_eq!(full, matrix(&[&[1, -1]]));
        for j in 0..2 {
            assert!(full.get(0, j).unwrap().abs() >= Rat::one());
            assert!(d.get(0, j).unwrap().abs() < Rat::one());
        }
        let f = matrix(&[&[1], &[0]]);
        let witness = matrix_product(&dual, &f).unwrap();
        assert_eq!(witness, matrix(&[&[1]]));
        assert_eq!(
            silence_verdict(witness.get(0, 0).unwrap(), &Rat::one()),
            SilenceVerdict::AtOrAboveWholeGrain
        );
        assert_eq!(max_row_sum(&dual), Rat::from_integer(2.into()));
    }

    #[test]
    fn grain_denominator_and_native_half_quantum_are_distinct() {
        let grain = Rat::new(BigInt::one(), BigInt::from(32));
        let half = &grain / Rat::from_integer(BigInt::from(2));
        assert_eq!(grain, Rat::new(1.into(), 32.into()));
        assert_eq!(half, Rat::new(1.into(), 64.into()));
        assert_ne!(grain, rat_pow2(-32));
    }

    #[test]
    fn metric_uses_stored_gram_without_adding_carry() {
        let h = matrix(&[&[5, 0], &[0, 3]]);
        let reasons = unconstrained_reasons(&[0, 1], 2, &[0, 1], 2, &h);
        assert!(reasons.is_empty());
        let constrained = unconstrained_reasons(&[0], 2, &[0], 2, &h);
        assert!(constrained.iter().any(|reason| reason.contains("support")));
        assert!(is_positive_definite(&h));
        assert!(!is_positive_definite(&matrix(&[&[1, 2], &[2, 1]])));
    }

    #[test]
    fn exact_column_bound_rounds_up_not_under() {
        let subunit = Matrix::new(vec![vec![Rat::new(3.into(), 4.into())]]).unwrap();
        assert_eq!(
            column_majorizer(&subunit).unwrap(),
            (vec![0], vec![Rat::one()])
        );
        let h = Matrix::new(vec![vec![Rat::new(3.into(), 2.into())]]).unwrap();
        assert_eq!(
            column_majorizer(&h).unwrap(),
            (vec![1], vec![Rat::from_integer(2.into())])
        );
    }

    #[test]
    fn report_lattice_empty_solved_support_is_a_valid_full_prior() {
        let law = NormalLaw::with_scaled_prior(Matrix::zero(4, 3).unwrap(), 2);
        assert!(law.chart().support().is_empty());
        assert_eq!(law.map().columns(), 3);
        assert_eq!(law.gram(), matrix(&[&[4, 0, 0], &[0, 4, 0], &[0, 0, 4]]));
        let quarter = Rat::new(1.into(), 4.into());
        assert_eq!(
            law.solved(),
            Matrix::new(vec![
                vec![quarter.clone(), Rat::zero(), Rat::zero()],
                vec![Rat::zero(), quarter.clone(), Rat::zero()],
                vec![Rat::zero(), Rat::zero(), quarter],
            ])
            .unwrap()
        );
        assert_eq!(
            specification_lattice_readout(32, law.chart().support(), 3, 10, 11).unwrap(),
            SpecificationLatticeReadout::UndefinedEmptySolvedSupport {
                declared_width: 3,
                receiver_exponent: 6,
            }
        );
        // The mathematical zero-width formula remains undefined, never replaced by width 1/3.
        assert!(spec_lattice_exponent(32, 0).is_err());
    }

    #[test]
    fn report_lattice_nonempty_reading_keeps_its_exact_formula_and_comparisons() {
        assert_eq!(
            specification_lattice_readout(32, &[0, 2], 3, 7, 11).unwrap(),
            SpecificationLatticeReadout::Defined {
                declared_width: 3,
                support_width: 2,
                receiver_exponent: 6,
                exponent: 7,
                unit: Rat::new(1.into(), 128.into()),
                native_cross_mismatch: false,
                native_end_mismatch: true,
            }
        );
    }

    #[test]
    fn report_lattice_undefined_comparison_does_not_hide_invalid_inputs() {
        assert!(specification_lattice_readout(0, &[], 3, 10, 11).is_err());
        assert!(specification_lattice_readout(32, &[], 0, 10, 11).is_err());
        assert!(specification_lattice_readout(32, &[3], 3, 10, 11).is_err());
        assert!(specification_lattice_readout(32, &[1, 1], 3, 10, 11).is_err());
        assert!(specification_lattice_readout(32, &[2, 1], 3, 10, 11).is_err());
    }

    #[test]
    fn native_and_spec_lattice_units_are_reported_independently() {
        let grain = 32;
        let spec = spec_lattice_exponent(grain, 32).unwrap();
        assert_eq!(amended_partition_receiver_exponent(grain).unwrap(), 6);
        assert_eq!(spec, 11);
        let native_cross = 37;
        let native_end = 39;
        assert_ne!(native_cross, spec);
        assert_ne!(native_end, spec);
        assert_eq!(
            rat_pow2(-i64::from(native_cross)),
            Rat::new(1.into(), BigInt::one() << 37usize)
        );
        assert_eq!(
            rat_pow2(-i64::from(native_end)),
            Rat::new(1.into(), BigInt::one() << 39usize)
        );
        assert_eq!(
            rat_pow2(-i64::from(spec)),
            Rat::new(1.into(), BigInt::one() << 11usize)
        );
        assert!(native_cross != spec);
        assert!(native_end != spec);
        assert_eq!(spec_lattice_exponent(3, 32).unwrap(), 8);
        assert!(spec_lattice_exponent(32, 0).is_err());
    }

    #[test]
    fn actual_sparse_release_closes_nonzero_stored_carry_and_sample_deltas() {
        // Two observed releases hit the same actual Gram coordinate across deposits; the aggregate
        // must use those native entries, not a value reconstructed from the balance remainder.
        let released = released_gram_entries(
            [
                (0, Rat::new(1.into(), 8.into())),
                (0, Rat::new(1.into(), 8.into())),
            ],
            1,
            1,
        )
        .unwrap();
        // The stored-H change contains one unit of native ridge change from scale 0 to 1.
        let stored_delta = Matrix::new(vec![vec![Rat::from_integer(2.into())]]).unwrap();
        let carry_delta = Matrix::new(vec![vec![Rat::new(1.into(), 4.into())]]).unwrap();
        let sample_delta = Matrix::new(vec![vec![Rat::new(3.into(), 2.into())]]).unwrap();
        let raw = matrix_subtract(
            &matrix_add(&stored_delta, &carry_delta).unwrap(),
            &sample_delta,
        )
        .unwrap();
        let raw_plus_release = matrix_add(&raw, &released).unwrap();
        let prior_delta = prior_gram_delta(1, 1, Some(2), Some(2), 0, 1)
            .unwrap()
            .unwrap();
        let adjusted_balance = matrix_subtract(&raw_plus_release, &prior_delta).unwrap();
        assert_eq!(
            released,
            Matrix::new(vec![vec![Rat::new(1.into(), 4.into())]]).unwrap()
        );
        assert_eq!(prior_delta, Matrix::new(vec![vec![Rat::one()]]).unwrap());
        assert_eq!(
            raw_plus_release,
            Matrix::new(vec![vec![Rat::one()]]).unwrap()
        );
        assert_eq!(adjusted_balance, Matrix::zero(1, 1).unwrap());
        assert!(
            prior_gram_delta(1, 1, Some(2), Some(3), 0, 1)
                .unwrap()
                .is_none()
        );
        assert!(prior_gram_delta(1, 1, None, None, 0, 1).unwrap().is_none());
    }

    #[test]
    fn conservation_failures_are_deferred_and_survive_fallback_finalization() {
        let mut unsupported = Vec::new();
        defer_conservation_verdict(&mut unsupported, false, false, &matrix(&[&[1]]));
        assert_eq!(unsupported.len(), 1);
        assert!(finish_deferred_failures(Vec::new()).is_ok());
        let unsupported_result = finish_deferred_failures(unsupported).unwrap_err();
        assert!(
            unsupported_result
                .to_string()
                .contains("conservation is unsupported")
        );

        let mut nonclosing = Vec::new();
        let nonzero_balance = Matrix::new(vec![vec![Rat::new(3.into(), 8.into())]]).unwrap();
        defer_conservation_verdict(&mut nonclosing, true, false, &nonzero_balance);
        // A fallback can record this verdict, finish its later held reads, then report it once.
        let nonclosing_result = finish_deferred_failures(nonclosing).unwrap_err();
        assert!(
            nonclosing_result
                .to_string()
                .contains("failed after exact prior adjustment")
        );
    }

    #[test]
    fn both_silence_bounds_use_whole_grain_boundary_inclusively() {
        let grain = Rat::new(1.into(), 32.into());
        let below = Rat::new(31.into(), 1024.into());
        let exact = grain.clone();
        let above = Rat::new(33.into(), 1024.into());
        assert_eq!(silence_verdict(&below, &grain), SilenceVerdict::BelowGrain);
        assert_eq!(
            silence_verdict(&exact, &grain),
            SilenceVerdict::AtOrAboveWholeGrain
        );
        assert_eq!(
            silence_verdict(&above, &grain),
            SilenceVerdict::AtOrAboveWholeGrain
        );
        // The two reportable enclosures each get their own verdict at the same grain q_R.
        let norm_bound = Rat::new(30.into(), 1024.into());
        let width_bound = Rat::new(32.into(), 1024.into());
        assert_eq!(
            silence_verdict(&norm_bound, &grain),
            SilenceVerdict::BelowGrain
        );
        assert_eq!(
            silence_verdict(&width_bound, &grain),
            SilenceVerdict::AtOrAboveWholeGrain
        );
    }

    #[test]
    fn paired_projected_gram_and_candidate_must_preserve_native_subspace() {
        let symmetry = PortSymmetry::from_parts(vec![1, 0], vec![Some(1), Some(0)], &[0]).unwrap();
        let h_projected = matrix(&[&[4, 1], &[1, 4]]);
        let delta_h_projected = matrix(&[&[2, -1], &[-1, 2]]);
        let candidate = matrix(&[&[3, 5], &[5, 3]]);
        assert!(gram_commutes_with_symmetry(&symmetry, &h_projected));
        assert!(gram_commutes_with_symmetry(&symmetry, &delta_h_projected));
        assert_eq!(symmetry.first_failure(&candidate).unwrap(), None);
        let unprojected = matrix(&[&[2, 0], &[0, 1]]);
        assert!(!gram_commutes_with_symmetry(&symmetry, &unprojected));
        assert!(symmetry.first_failure(&unprojected).unwrap().is_some());
    }

    #[test]
    fn nonpositive_fall_is_typed_only_for_nonzero_admitted_unconstrained_steps() {
        assert!(check_hypothetical_fall(true, true, &Rat::zero()).is_err());
        assert!(check_hypothetical_fall(true, true, &Rat::from_integer((-1).into())).is_err());
        assert!(check_hypothetical_fall(true, true, &Rat::one()).is_ok());
        assert!(check_hypothetical_fall(false, true, &Rat::zero()).is_ok());
        assert!(check_hypothetical_fall(true, false, &Rat::zero()).is_ok());
    }
}
