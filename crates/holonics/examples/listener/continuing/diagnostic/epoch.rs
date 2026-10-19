//! Exact, explicitly hypothetical one-epoch normal-law readout.
//!
//! This module does not claim access to the listener's private `PreparedStep.unit`, persistent
//! carry, or a device-certified gain. It forms `G_cross` from the retained frozen comparison
//! covectors and staged samples, then reports the unit-gain (`gamma = 1`) hypothetical law with
//! zero incoming residual. The native material Gram is the metric; the separately retained Gram
//! remainder is shown as carry and is never silently added to that metric.

use super::*;
use holonics::hnn::constitution::NormalLaw;
use holonics::hnn::paired::PortSymmetry;
use holonics::hnn::reference::FrozenComparison;
use holonics::ratio::algebraic::ExactInterval;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::fmt;

type Matrix = ExactRatMatrix;

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

fn exact_log2_power_of_two(value: &BigInt) -> Option<u32> {
    if value <= &BigInt::zero() {
        return None;
    }
    let bits = value.bits();
    let exponent = u32::try_from(bits.checked_sub(1)?).ok()?;
    (value == &(BigInt::one() << exponent as usize)).then_some(exponent)
}

pub(super) fn spec_lattice_exponent(receiver_grain: u64, support_width: usize) -> Result<u32> {
    let doubled_grain = receiver_grain
        .checked_mul(2)
        .ok_or("twice the receiver grain overflows u64")?;
    if receiver_grain == 0 || !doubled_grain.is_power_of_two() || support_width == 0 {
        return Err(
            "specification LW requires power-of-two 2*receiver grain and nonzero support width"
                .into(),
        );
    }
    let width = u64::try_from(support_width).map_err(|_| "support width exceeds u64")?;
    let ceil_width = if width.is_power_of_two() {
        width.trailing_zeros()
    } else {
        u64::BITS - width.leading_zeros()
    };
    doubled_grain
        .trailing_zeros()
        .checked_add(ceil_width)
        .ok_or_else(|| "specification LW overflows u32".into())
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
            "native Gram conservation failed after exact prior adjustment: ΔHstored + Δcarry - ΔsampleH + released - Δprior = {adjusted_balance:?}"
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
        let evaluation_result = (|| {
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
    let native_lw_cross = crossing.native_lattice_exponent;
    let native_lw_end = end.native_lattice_exponent;
    let width = crossing.support.len();
    let spec_lw = spec_lattice_exponent(receiver_grain, width)?;
    let spec_b_r = exact_log2_power_of_two(&(BigInt::from(receiver_grain) << 1usize));
    let spec_unit = rat_pow2(-i64::from(spec_lw));
    let native_unit_cross = rat_pow2(-i64::from(native_lw_cross));
    let native_unit_end = rat_pow2(-i64::from(native_lw_end));
    let native_spec_mismatch_cross = native_lw_cross != spec_lw;
    let native_spec_mismatch_end = native_lw_end != spec_lw;
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
        "step0_epoch_observables branch={branch} max_abs_f={max_feature} max_abs_live_sample_g={max_live_g} max_abs_input_crossing_g={max_sample_crossing_g} max_abs_G_cross_projected={} last_staged_sample_weight_as_newest_datum_weight={newest_sample_weight:?} age-derived_nu_weight=not_exposed zero_step_cells={zero_step_cells} vanished_map_cells={vanished_cells} native_LW_cross={native_lw_cross} native_W_unit_cross={native_unit_cross} native_vs_spec_LW_mismatch_cross={native_spec_mismatch_cross} native_LW_end={native_lw_end} native_W_unit_end={native_unit_end} native_vs_spec_LW_mismatch_end={native_spec_mismatch_end} spec_b_R=log2(2*L_R)={spec_b_r:?} spec_LW=b_R+ceil(log2(support_width={width}))={spec_lw} spec_W_unit={spec_unit:?} no_clock_feature_split_claimed",
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
    fn native_and_spec_lattice_units_are_reported_independently() {
        let grain = 32;
        let spec = spec_lattice_exponent(grain, 32).unwrap();
        assert_eq!(exact_log2_power_of_two(&(BigInt::from(2 * grain))), Some(6));
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
        assert!(spec_lattice_exponent(3, 32).is_err());
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
