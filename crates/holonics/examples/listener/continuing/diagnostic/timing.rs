//! Fixed-deadline timing and process-local observability for the step-0 diagnostic.
//!
//! The native phase uses the supervisor's Linux `CLOCK_MONOTONIC` deadlines. It reserves the
//! declared postwork interval inside the native cutoff; it cannot create or extend a deadline.

#[path = "exterior_clock.rs"]
mod exterior_clock;

use num_bigint::BigUint;
use num_traits::ToPrimitive;
use std::io;
use std::time::Instant;

const RUN_WALL_CAP_NS: u128 = 300_000_000_000;
const TERM_OFFSET_NS: u128 = 295_000_000_000;
const NATIVE_TERM_GRACE_NS: u128 = 5_000_000_000;
const REPORT_RESERVE_FLOOR_NS: u128 = 5_000_000_000;
const BLOCK_CELLS: usize = 8;

#[derive(Clone, Copy, Debug)]
struct DeadlineContract {
    started_ns: u128,
    term_ns: u128,
    total_ns: u128,
    native_ns: u128,
}

/// A shared immutable external deadline. Independent branch workers borrow this safely and
/// create separate mutable phase trackers; no timing mutex serializes their work.
#[derive(Clone, Debug)]
pub(super) struct RunBudget {
    deadline: DeadlineContract,
    reserve_ns: u128,
}

/// A narrower phase ceiling on the same supervisor-origin monotonic clock. It never changes
/// any supervisor deadline. Checks occur between atomic operations; the external supervisor
/// remains the hard process stop if one atomic operation outlasts a cooperative check.
#[derive(Clone, Debug)]
pub(crate) struct WorkCutoff {
    label: String,
    deadline_ns: u128,
}

impl WorkCutoff {
    /// Ordinary observed work borrows an absolute supervisor-origin monotonic deadline.
    /// This does not derive, extend or substitute a deadline from the current time.
    pub(crate) fn at_deadline(label: &str, deadline_ns: u128) -> io::Result<Self> {
        let cutoff = Self {
            label: label.to_owned(),
            deadline_ns,
        };
        cutoff.check()?;
        Ok(cutoff)
    }

    pub(crate) fn check(&self) -> io::Result<()> {
        self.check_at(exterior_clock::monotonic_ns()?)
    }

    fn check_at(&self, now_ns: u128) -> io::Result<()> {
        if now_ns >= self.deadline_ns {
            return Err(timed_out(format!(
                "{} stopped at its fixed phase ceiling; later cost phases must not start",
                self.label
            )));
        }
        Ok(())
    }

    pub(super) fn remaining_ns(&self) -> io::Result<u128> {
        Ok(self
            .deadline_ns
            .saturating_sub(exterior_clock::monotonic_ns()?))
    }
}

fn work_cutoff_at(
    label: &str,
    now_ns: u128,
    started_ns: u128,
    allowance_ns: u128,
    absolute_offset_ns: u128,
    shared_cutoff_ns: u128,
) -> io::Result<WorkCutoff> {
    if allowance_ns == 0 || absolute_offset_ns == 0 {
        return Err(invalid("a cost phase needs positive fixed ceilings"));
    }
    let deadline_ns = now_ns
        .checked_add(allowance_ns)
        .zip(started_ns.checked_add(absolute_offset_ns))
        .map(|(local, absolute)| local.min(absolute).min(shared_cutoff_ns))
        .ok_or_else(|| invalid("cost phase ceiling overflows monotonic nanoseconds"))?;
    let cutoff = WorkCutoff {
        label: label.to_owned(),
        deadline_ns,
    };
    cutoff.check_at(now_ns)?;
    Ok(cutoff)
}

impl RunBudget {
    /// Fixed local allowance and fixed offset from the supervisor start, both narrowed by
    /// the existing shared report cutoff. The caller's earlier phases cannot extend it.
    pub(super) fn cost_phase(
        &self,
        label: &str,
        allowance_ns: u128,
        absolute_offset_ns: u128,
    ) -> io::Result<WorkCutoff> {
        work_cutoff_at(
            label,
            exterior_clock::monotonic_ns()?,
            self.deadline.started_ns,
            allowance_ns,
            absolute_offset_ns,
            self.deadline
                .native_ns
                .saturating_sub(REPORT_RESERVE_FLOOR_NS),
        )
    }

    /// Loads the supervisor's absolute monotonic deadlines and reserves time for declared
    /// postwork. Missing/malformed environment values and non-Linux monotonic clocks fail closed.
    pub(super) fn new(reserve_ns: u128) -> io::Result<Self> {
        let deadline = DeadlineContract {
            started_ns: deadline_env("REQ063_SUPERVISOR_START_MONOTONIC_NS")?,
            term_ns: deadline_env("REQ063_TERM_DEADLINE_MONOTONIC_NS")?,
            total_ns: deadline_env("REQ063_TOTAL_DEADLINE_MONOTONIC_NS")?,
            native_ns: deadline_env("REQ063_NATIVE_DEADLINE_MONOTONIC_NS")?,
        };
        if deadline.term_ns.checked_sub(deadline.started_ns) != Some(TERM_OFFSET_NS)
            || deadline.total_ns.checked_sub(deadline.started_ns) != Some(RUN_WALL_CAP_NS)
            || deadline.term_ns.checked_sub(deadline.native_ns) != Some(NATIVE_TERM_GRACE_NS)
        {
            return Err(invalid(
                "supervisor deadlines do not match the fixed 295s TERM / 300s total / 5s native grace contract",
            ));
        }
        let now = exterior_clock::monotonic_ns()?;
        if now < deadline.started_ns || now >= deadline.native_ns {
            return Err(timed_out(
                "native process started outside its supervisor-provided execution window",
            ));
        }
        if reserve_ns >= deadline.native_ns - now {
            return Err(timed_out(
                "the explicit phase reserve does not fit before the native cutoff",
            ));
        }
        Ok(Self {
            deadline,
            reserve_ns,
        })
    }

    /// Opens a phase against the remaining native cutoff. Its allowance is fixed at entry and
    /// cannot be raised by later forecasts. The explicit phase cap can only narrow it.
    pub(super) fn phase(
        &self,
        label: &str,
        total_cells: usize,
        cap_ns: Option<u128>,
    ) -> io::Result<PhaseBudget> {
        if total_cells == 0 {
            return Err(invalid(
                "a timing phase must declare at least one work unit",
            ));
        }
        let now = exterior_clock::monotonic_ns()?;
        let available = self.global_remaining_ns_at(now);
        let phase_allowance_ns = cap_ns.map_or(available, |cap| cap.min(available));
        if phase_allowance_ns == 0 {
            return Err(timed_out(
                "no reserved native wall budget remains for this phase",
            ));
        }
        let phase_deadline_ns = now
            .checked_add(phase_allowance_ns)
            .ok_or_else(|| invalid("phase cutoff overflows monotonic nanoseconds"))?;
        Ok(PhaseBudget {
            label: label.to_owned(),
            started_ns: now,
            last_clock_ns: now,
            phase_deadline_ns,
            deadline: self.deadline,
            reserve_ns: self.reserve_ns,
            total_cells,
            completed_cells: 0,
            measured_cell_wall_ns: 0,
            block_cells: 0,
            block_wall_ns: 0,
            block_index: 0,
            forecast: ForecastBook::default(),
            consecutive_bad_blocks: 0,
            phase_allowance_ns,
            explicit_phase_cap: cap_ns.is_some(),
            stop_reason: None,
            summary_written: false,
        })
    }

    /// Remaining absolute native wall budget after the explicit postwork reserve. This uses the
    /// same supervisor-origin `CLOCK_MONOTONIC` cutoff as per-phase admission.
    pub(super) fn remaining_ns(&self) -> io::Result<u128> {
        let now = exterior_clock::monotonic_ns()?;
        Ok(self.global_remaining_ns_at(now))
    }

    /// Remaining time before the shared 285-second phase cutoff, retaining the fixed five
    /// second report floor before the native deadline.
    pub(super) fn remaining_report_ns(&self) -> io::Result<u128> {
        let now = exterior_clock::monotonic_ns()?;
        Ok(self
            .deadline
            .native_ns
            .saturating_sub(now)
            .saturating_sub(REPORT_RESERVE_FLOOR_NS))
    }

    fn global_remaining_ns_at(&self, now_ns: u128) -> u128 {
        self.deadline
            .native_ns
            .saturating_sub(now_ns)
            .saturating_sub(self.reserve_ns)
    }
}

/// A private synthetic-control clock; it reads no global environment and advances no learner.
#[cfg(test)]
pub(super) fn test_run_budget() -> io::Result<RunBudget> {
    let started_ns = exterior_clock::monotonic_ns()?;
    Ok(RunBudget {
        deadline: DeadlineContract {
            started_ns,
            term_ns: started_ns
                .checked_add(TERM_OFFSET_NS)
                .ok_or_else(|| invalid("test deadline overflow"))?,
            total_ns: started_ns
                .checked_add(RUN_WALL_CAP_NS)
                .ok_or_else(|| invalid("test deadline overflow"))?,
            native_ns: started_ns
                .checked_add(TERM_OFFSET_NS - NATIVE_TERM_GRACE_NS)
                .ok_or_else(|| invalid("test deadline overflow"))?,
        },
        reserve_ns: 0,
    })
}

#[derive(Clone, Copy, Debug)]
pub(super) enum ReportWorkKind {
    HeldEval,
    GramInverse,
    Other,
}

#[derive(Clone, Copy, Debug, Default)]
pub(super) struct WorkSummary {
    pub(super) count: usize,
    pub(super) total_ns: u128,
    pub(super) max_ns: u128,
}

#[derive(Clone, Debug)]
pub(super) struct ReportSummary {
    pub(super) branch: String,
    pub(super) held_eval: WorkSummary,
    pub(super) gram_inverse: WorkSummary,
    pub(super) other: WorkSummary,
    pub(super) elapsed_ns: u128,
    pub(super) projected_231_ns: Option<u128>,
    pub(super) remaining_report_ns: u128,
}

/// Per-branch accounting for read-only report work. Trackers share the immutable supervisor
/// deadline but never serialize branch work through a shared lock.
pub(super) struct ReportBudget {
    run: RunBudget,
    branch: String,
    started: Instant,
    held_eval: Vec<u128>,
    gram_inverse: Vec<u128>,
    other: Vec<u128>,
    cutoff: Option<WorkCutoff>,
}

impl ReportBudget {
    pub(super) fn new(run: &RunBudget, branch: &str, _measured_cells: usize) -> Self {
        Self {
            run: run.clone(),
            branch: branch.to_owned(),
            started: Instant::now(),
            held_eval: Vec::new(),
            gram_inverse: Vec::new(),
            other: Vec::new(),
            cutoff: None,
        }
    }

    pub(super) fn with_cutoff(mut self, cutoff: &WorkCutoff) -> Self {
        self.cutoff = Some(cutoff.clone());
        self
    }

    pub(super) fn check_before_work(&self, label: &str) -> io::Result<()> {
        if let Some(cutoff) = &self.cutoff {
            cutoff.check()?;
        }
        if self.run.remaining_report_ns()? == 0 {
            return Err(timed_out(format!(
                "branch {} cannot start {label}: the shared 285-second phase cutoff was reached (five-second report floor)",
                self.branch
            )));
        }
        Ok(())
    }

    pub(super) fn remaining_ns(&self) -> io::Result<u128> {
        let shared = self.run.remaining_report_ns()?;
        match &self.cutoff {
            Some(cutoff) => Ok(shared.min(cutoff.remaining_ns()?)),
            None => Ok(shared),
        }
    }

    pub(super) fn record_work(&mut self, kind: ReportWorkKind, elapsed_ns: u128) {
        match kind {
            ReportWorkKind::HeldEval => self.held_eval.push(elapsed_ns),
            ReportWorkKind::GramInverse => self.gram_inverse.push(elapsed_ns),
            ReportWorkKind::Other => self.other.push(elapsed_ns),
        }
    }

    pub(super) fn finish(&mut self) -> ReportSummary {
        let held_eval = work_summary(&self.held_eval);
        let gram_inverse = work_summary(&self.gram_inverse);
        let other = work_summary(&self.other);
        // Report work depends on exact rational bit growth and on the report variant. A
        // calibration count supplies no model for a different population. Keep the raw
        // measurements; only the separately pinned empirical admission input may forecast 231.
        let projected_231_ns = None;
        let remaining_report_ns = self.remaining_ns().unwrap_or(0);
        ReportSummary {
            branch: self.branch.clone(),
            held_eval,
            gram_inverse,
            other,
            elapsed_ns: self.started.elapsed().as_nanos(),
            projected_231_ns,
            remaining_report_ns,
        }
    }
}

fn work_summary(values: &[u128]) -> WorkSummary {
    WorkSummary {
        count: values.len(),
        total_ns: values.iter().copied().fold(0, u128::saturating_add),
        max_ns: values.iter().copied().max().unwrap_or(0),
    }
}

/// Externally pinned, empirical report-cost input. This is a feasibility forecast, never a
/// mathematical upper bound or a completion certificate. In particular, increasing measured
/// populations do not bound future rational bit growth. The source hash identifies the report
/// implementation/tree; the input hash identifies the exact captured operands. Measurements
/// must run that implementation and report variant, including its complete corrected series.
///
/// `REQ063_REPORT_GROWTH_INPUT` uses newline-delimited `key=value` fields, exactly once each:
/// source_sha256, input_sha256, report_variant, measurements (`16:ns,32:ns,64:ns`, for example),
/// target_cells (`231`), projected_report_ns (the pinned complete per-branch cost),
/// forecast_description (formula, inputs and future rational-bit-growth scope), adequacy
/// (`empirical_forecast` or `uncertain`), checkpoint_reserve_ns, aa0_postwork_reserve_ns.
/// Missing, duplicate and unknown fields fail closed. The 16/32/64 timings are mandatory:
/// the proposal must cover their exact empirical doubling-growth floor, without turning that
/// extrapolation into a mathematical bound on future rational bit growth.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReportAdmission {
    pub(super) source_sha256: String,
    pub(super) input_sha256: String,
    pub(super) report_variant: String,
    pub(super) measurements: Vec<ReportGrowthMeasurement>,
    pub(super) empirical_growth: EmpiricalReportGrowth,
    pub(super) target_cells: usize,
    pub(super) projected_report_ns: u128,
    pub(super) forecast_description: String,
    pub(super) checkpoint_reserve_ns: u128,
    pub(super) aa0_postwork_reserve_ns: u128,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReportGrowthMeasurement {
    pub(super) cells: usize,
    pub(super) report_ns: u128,
}

/// An empirical forecast from the two measured doublings, not an upper-bound certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct EmpiricalReportGrowth {
    pub(super) exponent: u32,
    pub(super) floor_231_ns: u128,
    pub(super) measured_64_ns: u128,
}

impl EmpiricalReportGrowth {
    /// Keep the measured/projected comparison as its exact undivided pair, in nanoseconds.
    pub(super) fn measured_to_projected_ratio(
        &self,
        projected_ns: u128,
    ) -> io::Result<(u128, u128)> {
        if projected_ns == 0 {
            return Err(invalid(
                "a measured-to-projected ratio needs a positive projection",
            ));
        }
        Ok((self.measured_64_ns, projected_ns))
    }
}

/// Smallest integer e >= 1 with r32 <= r16 * 2^e and r64 <= r32 * 2^e, followed by
/// ceil(r64 * 231^e / 64^e). BigUint keeps the shifted comparisons and powers exact even
/// when an intermediate exceeds u128. Positive u128 timings need at most e = 128; only an
/// unrepresentable final nanosecond floor is refused. This forecasts the declared report
/// variant empirically and establishes no law of future arithmetic cost.
pub(super) fn empirical_report_growth_floor(
    r16_ns: u128,
    r32_ns: u128,
    r64_ns: u128,
) -> io::Result<EmpiricalReportGrowth> {
    if r16_ns == 0 || r32_ns == 0 || r64_ns == 0 {
        return Err(invalid(
            "empirical report growth requires positive 16/32/64 timings",
        ));
    }
    let r16 = BigUint::from(r16_ns);
    let r32 = BigUint::from(r32_ns);
    let r64 = BigUint::from(r64_ns);
    let exponent = (1_u32..=u128::BITS)
        .find(|&exponent| r32 <= (&r16 << exponent as usize) && r64 <= (&r32 << exponent as usize))
        .ok_or_else(|| invalid("empirical report doubling exponent is unrepresentable"))?;
    let numerator = r64 * BigUint::from(231_u16).pow(exponent);
    let denominator = BigUint::from(64_u8).pow(exponent);
    let floor = (&numerator + &denominator - BigUint::from(1_u8)) / denominator;
    let floor_231_ns = floor.to_u128().ok_or_else(|| {
        invalid("empirical 231-cell report-growth floor exceeds u128 nanoseconds")
    })?;
    Ok(EmpiricalReportGrowth {
        exponent,
        floor_231_ns,
        measured_64_ns: r64_ns,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReportAdmissionSummary {
    pub(super) one_branch_combined_ns: u128,
    pub(super) fork_horizon_ns: u128,
    pub(super) checkpoint_reserve_ns: u128,
    pub(super) aa0_postwork_reserve_ns: u128,
    pub(super) total_required_ns: u128,
}

impl ReportAdmission {
    pub(super) fn from_env() -> io::Result<Self> {
        let text = std::env::var("REQ063_REPORT_GROWTH_INPUT")
            .map_err(|_| invalid("required pinned REQ063_REPORT_GROWTH_INPUT is missing"))?;
        Self::parse(&text)
    }

    fn parse(text: &str) -> io::Result<Self> {
        use std::collections::BTreeMap;
        let names = [
            "source_sha256",
            "input_sha256",
            "report_variant",
            "measurements",
            "target_cells",
            "projected_report_ns",
            "forecast_description",
            "adequacy",
            "checkpoint_reserve_ns",
            "aa0_postwork_reserve_ns",
        ];
        let mut fields = BTreeMap::new();
        for line in text.lines() {
            let (key, value) = line
                .split_once('=')
                .ok_or_else(|| invalid("report-growth input requires key=value lines"))?;
            if !names.contains(&key) || value.trim().is_empty() {
                return Err(invalid(format!(
                    "unknown or empty report-growth field {key:?}"
                )));
            }
            if fields.insert(key, value).is_some() {
                return Err(invalid(format!("duplicate report-growth field {key}")));
            }
        }
        let field = |key| {
            fields
                .get(key)
                .copied()
                .ok_or_else(|| invalid(format!("required report-growth field {key} is missing")))
        };
        let positive = |key| -> io::Result<u128> {
            field(key)?
                .parse::<u128>()
                .ok()
                .filter(|&value| value > 0)
                .ok_or_else(|| {
                    invalid(format!(
                        "report-growth {key} must be positive unsigned nanoseconds"
                    ))
                })
        };
        for key in ["source_sha256", "input_sha256"] {
            let hash = field(key)?;
            if hash.len() != 64 || !hash.bytes().all(|byte| byte.is_ascii_hexdigit()) {
                return Err(invalid(format!(
                    "report-growth {key} must be a full SHA-256 digest"
                )));
            }
        }
        if field("adequacy")? != "empirical_forecast" {
            return Err(invalid(
                "report-growth adequacy is uncertain or unsupported; refusing admission",
            ));
        }
        let target_cells = field("target_cells")?
            .parse::<usize>()
            .map_err(|_| invalid("report-growth target_cells is not an unsigned count"))?;
        if target_cells != 231 {
            return Err(invalid(
                "report-growth target_cells must match the declared 231-cell branch",
            ));
        }
        let mut measurements = Vec::new();
        for measurement in field("measurements")?.split(',') {
            let (count, elapsed) = measurement
                .split_once(':')
                .ok_or_else(|| invalid("report-growth measurements require cells:report_ns"))?;
            let cells = count
                .parse::<usize>()
                .map_err(|_| invalid("report-growth measurement count is not unsigned"))?;
            let report_ns = elapsed.parse::<u128>().map_err(|_| {
                invalid("report-growth measurement timing is not unsigned nanoseconds")
            })?;
            if cells == 0
                || cells > target_cells
                || report_ns == 0
                || measurements
                    .last()
                    .is_some_and(|previous: &ReportGrowthMeasurement| previous.cells >= cells)
            {
                return Err(invalid(
                    "report-growth measurements need positive timings and strictly increasing positive counts no larger than the target",
                ));
            }
            measurements.push(ReportGrowthMeasurement { cells, report_ns });
        }
        if measurements.len() < 3 {
            return Err(invalid(
                "report-growth forecast requires at least three measured populations",
            ));
        }
        let measured = |cells| {
            measurements
                .iter()
                .find(|measurement| measurement.cells == cells)
                .map(|measurement| measurement.report_ns)
                .ok_or_else(|| {
                    invalid(format!(
                        "report-growth measurement at {cells} cells is missing"
                    ))
                })
        };
        let empirical_growth =
            empirical_report_growth_floor(measured(16)?, measured(32)?, measured(64)?)?;
        let projected_report_ns = positive("projected_report_ns")?;
        if projected_report_ns < empirical_growth.floor_231_ns {
            return Err(invalid(format!(
                "report-growth proposal {projected_report_ns} ns is below the empirical 231-cell floor {} ns at doubling exponent {}",
                empirical_growth.floor_231_ns, empirical_growth.exponent
            )));
        }
        if measurements
            .iter()
            .any(|measurement| measurement.report_ns > projected_report_ns)
        {
            return Err(invalid(
                "report-growth proposal is below a measured complete report cost",
            ));
        }
        let model = Self {
            source_sha256: field("source_sha256")?.to_owned(),
            input_sha256: field("input_sha256")?.to_owned(),
            report_variant: field("report_variant")?.to_owned(),
            measurements,
            empirical_growth,
            target_cells,
            projected_report_ns,
            forecast_description: field("forecast_description")?.to_owned(),
            checkpoint_reserve_ns: positive("checkpoint_reserve_ns")?,
            aa0_postwork_reserve_ns: positive("aa0_postwork_reserve_ns")?,
        };
        // Validate the reserve series itself before a caller can consume the forecast.
        model
            .checkpoint_reserve_ns
            .checked_add(model.aa0_postwork_reserve_ns)
            .and_then(|reserves| reserves.checked_add(model.projected_report_ns))
            .ok_or_else(|| {
                invalid("report-growth cost and reserve series overflows nanoseconds")
            })?;
        Ok(model)
    }

    pub(super) fn report_projection_ns(&self) -> u128 {
        self.projected_report_ns
    }

    pub(super) fn admit(
        &self,
        native_per_branch_ns: u128,
        branch_waves: usize,
        remaining_phase_ns: u128,
        branch_cap_ns: u128,
    ) -> io::Result<ReportAdmissionSummary> {
        self.admit_with_checkpoint(
            native_per_branch_ns,
            branch_waves,
            remaining_phase_ns,
            branch_cap_ns,
            self.checkpoint_reserve_ns,
        )
    }

    /// The checkpoint has already completed; its actual elapsed time must already have been
    /// deducted by reading the same immutable supervisor clock. Only its pending reserve goes.
    pub(super) fn admit_after_checkpoint(
        &self,
        native_per_branch_ns: u128,
        branch_waves: usize,
        remaining_phase_ns: u128,
        branch_cap_ns: u128,
    ) -> io::Result<ReportAdmissionSummary> {
        self.admit_with_checkpoint(
            native_per_branch_ns,
            branch_waves,
            remaining_phase_ns,
            branch_cap_ns,
            0,
        )
    }

    fn admit_with_checkpoint(
        &self,
        native_per_branch_ns: u128,
        branch_waves: usize,
        remaining_phase_ns: u128,
        branch_cap_ns: u128,
        checkpoint_reserve_ns: u128,
    ) -> io::Result<ReportAdmissionSummary> {
        if native_per_branch_ns == 0 || branch_waves == 0 || branch_cap_ns == 0 {
            return Err(invalid(
                "report admission needs positive native cost, branch waves and cap",
            ));
        }
        let one_branch_combined_ns = native_per_branch_ns
            .checked_add(self.projected_report_ns)
            .ok_or_else(|| invalid("native-plus-report branch forecast overflows nanoseconds"))?;
        let fork_horizon_ns = one_branch_combined_ns
            .checked_mul(branch_waves as u128)
            .ok_or_else(|| invalid("native-plus-report fork forecast overflows nanoseconds"))?;
        let total_required_ns = fork_horizon_ns
            .checked_add(checkpoint_reserve_ns)
            .and_then(|horizon| horizon.checked_add(self.aa0_postwork_reserve_ns))
            .ok_or_else(|| {
                invalid("fork forecast and explicit postwork reserves overflow nanoseconds")
            })?;
        if one_branch_combined_ns > branch_cap_ns || total_required_ns > remaining_phase_ns {
            return Err(timed_out(format!(
                "empirical native-plus-report forecast does not fit: branch_ns={one_branch_combined_ns} branch_cap_ns={branch_cap_ns} fork_ns={fork_horizon_ns} checkpoint_reserve_ns={checkpoint_reserve_ns} aa0_postwork_reserve_ns={} total_required_ns={total_required_ns} remaining_phase_ns={remaining_phase_ns}; fixed deadline unchanged",
                self.aa0_postwork_reserve_ns
            )));
        }
        Ok(ReportAdmissionSummary {
            one_branch_combined_ns,
            fork_horizon_ns,
            checkpoint_reserve_ns,
            aa0_postwork_reserve_ns: self.aa0_postwork_reserve_ns,
            total_required_ns,
        })
    }
}

pub(super) fn fork_and_report_projection(
    native_per_branch_ns: u128,
    report_per_branch_ns: u128,
    branch_waves: usize,
) -> u128 {
    native_per_branch_ns
        .saturating_add(report_per_branch_ns)
        .saturating_mul(branch_waves as u128)
}

pub(super) fn projection_fits(
    native_per_branch_ns: u128,
    report_per_branch_ns: u128,
    branch_waves: usize,
    remaining_phase_ns: u128,
    branch_cap_ns: u128,
) -> bool {
    if branch_waves == 0 {
        return false;
    }
    native_per_branch_ns
        .checked_add(report_per_branch_ns)
        .filter(|&branch| branch <= branch_cap_ns)
        .and_then(|branch| branch.checked_mul(branch_waves as u128))
        .is_some_and(|horizon| horizon <= remaining_phase_ns)
}

/// Per-phase mutable accounting. One instance belongs to one worker. Dropping it before explicit
/// completion writes an incomplete summary, including a partial block and a reason.
#[derive(Debug)]
pub(super) struct PhaseBudget {
    label: String,
    started_ns: u128,
    last_clock_ns: u128,
    phase_deadline_ns: u128,
    deadline: DeadlineContract,
    reserve_ns: u128,
    total_cells: usize,
    completed_cells: usize,
    measured_cell_wall_ns: u128,
    block_cells: usize,
    block_wall_ns: u128,
    block_index: usize,
    forecast: ForecastBook,
    consecutive_bad_blocks: usize,
    phase_allowance_ns: u128,
    explicit_phase_cap: bool,
    stop_reason: Option<String>,
    summary_written: bool,
}

impl PhaseBudget {
    /// Check actual native/phase time and whether the latest completed-block upper estimate can
    /// fit the next declared unit. Call before starting that unit.
    pub(super) fn before_cell(&mut self) -> io::Result<()> {
        if let Some(reason) = &self.stop_reason {
            return Err(timed_out(reason.clone()));
        }
        if self.completed_cells >= self.total_cells {
            return Err(self.stop_error("phase has no declared work units remaining"));
        }
        let now = match exterior_clock::monotonic_ns() {
            Ok(now) => now,
            Err(error) => {
                return Err(self.stop_error(format!("monotonic clock unavailable: {error}")));
            }
        };
        self.last_clock_ns = now;
        let phase_left = self.phase_deadline_ns.saturating_sub(now);
        let native_left = self.native_remaining_ns_at(now);
        if phase_left == 0 || native_left == 0 || now >= self.deadline.native_ns {
            return Err(self.stop_error(format!(
                "{} stopped before cell {}: fixed native/phase cutoff reached",
                self.label,
                self.completed_cells + 1
            )));
        }
        if let Some(upper_ns_per_cell) = self.forecast.upper_ns_per_cell() {
            if phase_left <= upper_ns_per_cell || native_left <= upper_ns_per_cell {
                return Err(self.stop_error(format!(
                    "{} stopped before cell {}: remaining hard budget cannot fit the next declared unit (forecast upper {} ns)",
                    self.label,
                    self.completed_cells + 1,
                    upper_ns_per_cell
                )));
            }
        }
        if self.consecutive_bad_blocks >= 2 {
            return Err(self.stop_error(format!(
                "{} stopped before cell {}: projected exhaustion persisted for two completed blocks",
                self.label,
                self.completed_cells + 1
            )));
        }
        Ok(())
    }

    /// Records a completed native unit. An individual cell's duration never triggers an abort.
    /// An explicit fixed cap admits only cap/declared-count per cell: its first completed
    /// eight-cell block above that rate stops immediately. Uncapped forecasts retain their
    /// two-block rule; the final partial block is reported separately.
    pub(super) fn finish_cell(&mut self, cell_ns: u128) -> io::Result<()> {
        if let Some(reason) = &self.stop_reason {
            return Err(timed_out(reason.clone()));
        }
        if self.completed_cells >= self.total_cells {
            return Err(self.stop_error("more completed cells than the phase declared"));
        }
        self.completed_cells += 1;
        self.measured_cell_wall_ns = self.measured_cell_wall_ns.saturating_add(cell_ns);
        self.block_cells += 1;
        self.block_wall_ns = self.block_wall_ns.saturating_add(cell_ns);
        if self.block_cells == BLOCK_CELLS {
            self.block_index += 1;
            self.forecast.push(self.block_wall_ns);
            if let Err(error) = self.update_projection_streak() {
                return Err(
                    self.stop_error(format!("monotonic clock unavailable after cell: {error}"))
                );
            }
            let exceeds_admitted_rate = self.explicit_phase_cap
                && completed_block_exceeds_admitted_rate(
                    self.block_wall_ns,
                    self.phase_allowance_ns,
                    self.total_cells,
                );
            self.report_block(false);
            self.block_cells = 0;
            self.block_wall_ns = 0;
            if exceeds_admitted_rate {
                return Err(self.stop_error(format!(
                    "{} stopped after completed eight-cell block {}: measured block rate exceeds the fixed pre-admitted per-cell rate {}/{} ns; deadline unchanged",
                    self.label, self.block_index, self.phase_allowance_ns, self.total_cells
                )));
            }
        }
        let now = match exterior_clock::monotonic_ns() {
            Ok(now) => now,
            Err(error) => {
                return Err(
                    self.stop_error(format!("monotonic clock unavailable after cell: {error}"))
                );
            }
        };
        self.last_clock_ns = now;
        if now >= self.phase_deadline_ns || now >= self.deadline.native_ns {
            return Err(self.stop_error(format!(
                "{} crossed its fixed native cutoff while completing cell {}",
                self.label, self.completed_cells
            )));
        }
        Ok(())
    }

    /// Mark a caller-detected failure or early stop so Drop can emit a truthful incomplete receipt.
    pub(super) fn mark_stop(&mut self, reason: impl Into<String>) {
        self.stop_reason = Some(reason.into());
    }

    /// Emits final partial-block and phase summary and returns the summary to the parent.
    pub(super) fn finish_phase(mut self) -> PhaseSummary {
        if self.completed_cells < self.total_cells && self.stop_reason.is_none() {
            self.stop_reason = Some("phase ended before its declared work count".to_owned());
        }
        let summary = self.summary();
        self.write_summary();
        self.summary_written = true;
        summary
    }

    fn stop_error(&mut self, reason: impl Into<String>) -> io::Error {
        let reason = reason.into();
        self.stop_reason = Some(reason.clone());
        timed_out(reason)
    }

    fn native_remaining_ns_at(&self, now_ns: u128) -> u128 {
        self.deadline
            .native_ns
            .saturating_sub(now_ns)
            .saturating_sub(self.reserve_ns)
    }

    fn update_projection_streak(&mut self) -> io::Result<()> {
        let Some(upper_ns_per_cell) = self.forecast.upper_ns_per_cell() else {
            return Ok(());
        };
        let now = exterior_clock::monotonic_ns()?;
        self.last_clock_ns = now;
        let remaining_cells = self.total_cells.saturating_sub(self.completed_cells) as u128;
        let projected = now
            .saturating_sub(self.started_ns)
            .saturating_add(upper_ns_per_cell.saturating_mul(remaining_cells));
        if projected > self.phase_allowance_ns {
            self.consecutive_bad_blocks = self.consecutive_bad_blocks.saturating_add(1);
        } else {
            self.consecutive_bad_blocks = 0;
        }
        Ok(())
    }

    fn elapsed_ns(&self) -> u128 {
        exterior_clock::monotonic_ns()
            .map(|now| now.saturating_sub(self.started_ns))
            .unwrap_or_else(|_| self.last_clock_ns.saturating_sub(self.started_ns))
    }

    fn projected_ns(&self) -> Option<u128> {
        let rate = self.forecast.upper_ns_per_cell()?;
        Some(self.elapsed_ns().saturating_add(
            rate.saturating_mul(self.total_cells.saturating_sub(self.completed_cells) as u128),
        ))
    }

    fn summary(&self) -> PhaseSummary {
        phase_summary_from_measurements(
            self.label.clone(),
            self.completed_cells,
            self.total_cells,
            self.elapsed_ns(),
            self.measured_cell_wall_ns,
            self.phase_allowance_ns,
            self.forecast.upper_ns_per_cell(),
            self.consecutive_bad_blocks,
            self.stop_reason.clone(),
        )
    }

    fn report_block(&self, partial: bool) {
        let forecast = self.forecast.snapshot();
        let (mean_num, mean_den, spread_num, spread_den, upper) =
            forecast.map_or((None, None, None, None, None), |f| {
                (
                    Some(f.mean_numerator_ns),
                    Some(f.mean_denominator),
                    Some(f.spread_numerator_ns),
                    Some(f.spread_denominator),
                    Some(f.upper_ns_per_cell),
                )
            });
        eprintln!(
            "timing phase={} block={} cells={} wall_ns={} partial={} completed={} elapsed_wall_ns={} phase_allowance_ns={} M={:?}/{:?}ns_per_cell S={:?}/{:?}ns_per_cell ceil(M+S)={:?}ns_per_cell remaining_cells={} projected_ns={:?} bad_block_streak={}",
            self.label,
            self.block_index + usize::from(partial),
            self.block_cells.max(if partial { 0 } else { BLOCK_CELLS }),
            self.block_wall_ns,
            partial,
            self.completed_cells,
            self.elapsed_ns(),
            self.phase_allowance_ns,
            mean_num,
            mean_den,
            spread_num,
            spread_den,
            upper,
            self.total_cells.saturating_sub(self.completed_cells),
            self.projected_ns(),
            self.consecutive_bad_blocks,
        );
    }

    fn write_summary(&self) {
        if self.block_cells > 0 {
            self.report_block(true);
        }
        let summary = self.summary();
        eprintln!(
            "timing phase_summary phase={} status={} reason={:?} completed={} declared={} elapsed_wall_ns={} measured_cell_wall_ns={} mean_cell_wall_ns={:?}/{:?} forecast_upper_ns_per_cell={:?} projected_ns={:?} fixed_phase_allowance_ns={} bad_block_streak={}",
            summary.label,
            if summary.incomplete {
                "incomplete"
            } else {
                "complete"
            },
            summary.stop_reason,
            summary.completed_cells,
            summary.declared_cells,
            summary.elapsed_wall_ns,
            summary.measured_cell_wall_ns,
            (summary.completed_cells > 0).then_some(summary.measured_cell_wall_ns),
            (summary.completed_cells > 0).then_some(summary.completed_cells),
            summary.forecast_upper_ns_per_cell,
            summary.projected_ns,
            summary.phase_allowance_ns,
            summary.consecutive_bad_blocks,
        );
    }
}

fn completed_block_exceeds_admitted_rate(
    block_wall_ns: u128,
    phase_allowance_ns: u128,
    declared_cells: usize,
) -> bool {
    match block_wall_ns
        .checked_mul(declared_cells as u128)
        .zip(phase_allowance_ns.checked_mul(BLOCK_CELLS as u128))
    {
        Some((measured, admitted)) => measured > admitted,
        None => {
            BigUint::from(block_wall_ns) * BigUint::from(declared_cells)
                > BigUint::from(phase_allowance_ns) * BigUint::from(BLOCK_CELLS)
        }
    }
}

impl Drop for PhaseBudget {
    fn drop(&mut self) {
        if self.summary_written {
            return;
        }
        if self.stop_reason.is_none() {
            self.stop_reason = Some("phase dropped before explicit finish".to_owned());
        }
        self.write_summary();
        self.summary_written = true;
    }
}

/// End-of-phase accounting, including an explicit incomplete reason and measured rate operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PhaseSummary {
    pub(super) label: String,
    pub(super) completed_cells: usize,
    pub(super) declared_cells: usize,
    pub(super) elapsed_wall_ns: u128,
    pub(super) measured_cell_wall_ns: u128,
    pub(super) phase_allowance_ns: u128,
    pub(super) forecast_upper_ns_per_cell: Option<u128>,
    pub(super) projected_ns: Option<u128>,
    pub(super) consecutive_bad_blocks: usize,
    pub(super) incomplete: bool,
    pub(super) stop_reason: Option<String>,
}

fn phase_summary_from_measurements(
    label: String,
    completed_cells: usize,
    declared_cells: usize,
    elapsed_wall_ns: u128,
    measured_cell_wall_ns: u128,
    phase_allowance_ns: u128,
    forecast_upper_ns_per_cell: Option<u128>,
    consecutive_bad_blocks: usize,
    stop_reason: Option<String>,
) -> PhaseSummary {
    let incomplete = completed_cells != declared_cells || stop_reason.is_some();
    let projected_ns = forecast_upper_ns_per_cell.map(|rate| {
        elapsed_wall_ns.saturating_add(
            rate.saturating_mul(declared_cells.saturating_sub(completed_cells) as u128),
        )
    });
    PhaseSummary {
        label,
        completed_cells,
        declared_cells,
        elapsed_wall_ns,
        measured_cell_wall_ns,
        phase_allowance_ns,
        forecast_upper_ns_per_cell,
        projected_ns,
        consecutive_bad_blocks,
        incomplete,
        stop_reason: stop_reason.or_else(|| {
            incomplete.then(|| "phase ended before its declared work count".to_owned())
        }),
    }
}

fn deadline_env(name: &str) -> io::Result<u128> {
    std::env::var(name)
        .map_err(|_| invalid(format!("required supervisor deadline {name} is missing")))?
        .parse::<u128>()
        .map_err(|_| {
            invalid(format!(
                "required supervisor deadline {name} is not unsigned nanoseconds"
            ))
        })
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.into())
}

fn timed_out(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::TimedOut, message.into())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Forecast {
    mean_numerator_ns: u128,
    mean_denominator: u128,
    spread_numerator_ns: u128,
    spread_denominator: u128,
    upper_ns_per_cell: u128,
}

/// Fixed-block rates only. `M` is the exact arithmetic mean of completed block rates and `S` is
/// max minus min block rate; for the fixed 8-cell blocks, both share a rational denominator.
#[derive(Clone, Debug, Default)]
struct ForecastBook {
    block_wall_ns: Vec<u128>,
}

/// Estimate `ceil(M + S)` from fixed completed eight-cell blocks. An incomplete tail is
/// deliberately ignored; a single cell is never itself a forecast or an abort threshold.
pub(super) fn completed_block_upper_ns_per_cell(cell_times: &[u128]) -> Option<u128> {
    let mut forecast = ForecastBook::default();
    for cells in cell_times.chunks_exact(BLOCK_CELLS) {
        let block_wall_ns = cells
            .iter()
            .try_fold(0_u128, |sum, &cell_ns| sum.checked_add(cell_ns))?;
        forecast.push(block_wall_ns);
    }
    forecast.upper_ns_per_cell()
}

impl ForecastBook {
    fn push(&mut self, block_wall_ns: u128) {
        self.block_wall_ns.push(block_wall_ns);
    }

    fn upper_ns_per_cell(&self) -> Option<u128> {
        self.snapshot().map(|forecast| forecast.upper_ns_per_cell)
    }

    fn snapshot(&self) -> Option<Forecast> {
        let count = self.block_wall_ns.len() as u128;
        if count == 0 {
            return None;
        }
        let sum = self
            .block_wall_ns
            .iter()
            .try_fold(0_u128, |sum, &wall| sum.checked_add(wall))?;
        let max = *self.block_wall_ns.iter().max()?;
        let min = *self.block_wall_ns.iter().min()?;
        let denominator = count.checked_mul(BLOCK_CELLS as u128)?;
        let spread_at_mean_denominator = max.checked_sub(min)?.checked_mul(count)?;
        let numerator = sum.checked_add(spread_at_mean_denominator)?;
        let upper = div_ceil(numerator, denominator)?;
        Some(Forecast {
            mean_numerator_ns: sum,
            mean_denominator: denominator,
            spread_numerator_ns: max - min,
            spread_denominator: BLOCK_CELLS as u128,
            upper_ns_per_cell: upper,
        })
    }
}

/// Per-thread CPU counters are raw Linux clock ticks. Resolution is supplied only when the
/// caller provides `REQ063_CLK_TCK`; this module does not guess a system tick rate. Scheduler
/// waiting time is reported as a separate counter, never classified automatically as OS jitter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ThreadCpu {
    pub(super) user_ticks: u64,
    pub(super) system_ticks: u64,
    pub(super) ticks_per_second: Option<u64>,
    pub(super) scheduler: Option<ThreadSchedulerTime>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ThreadCpuDelta {
    pub(super) user_ticks: u64,
    pub(super) system_ticks: u64,
    pub(super) ticks_per_second: Option<u64>,
    pub(super) scheduler: Option<ThreadSchedulerDelta>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ThreadSchedulerTime {
    pub(super) running_ns: u64,
    pub(super) waiting_ns: u64,
    pub(super) timeslices: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ThreadSchedulerDelta {
    pub(super) running_ns: u64,
    pub(super) waiting_ns: u64,
    pub(super) timeslices: u64,
}

impl ThreadCpu {
    /// Read `/proc/thread-self/stat` and optional `/proc/thread-self/schedstat`. Missing files,
    /// malformed counters, or an unavailable Linux procfs return `None` rather than invented data.
    pub(super) fn read() -> Option<Self> {
        #[cfg(target_os = "linux")]
        {
            // Procfs is exterior telemetry, read through the example's explicit I/O boundary.
            let stat = crate::octets::read("/proc/thread-self/stat").ok()?;
            let (user_ticks, system_ticks) = parse_thread_stat(std::str::from_utf8(&stat).ok()?)?;
            let ticks_per_second = std::env::var("REQ063_CLK_TCK")
                .ok()
                .and_then(|value| parse_ticks_per_second(&value));
            let scheduler = crate::octets::read("/proc/thread-self/schedstat")
                .ok()
                .and_then(|value| std::str::from_utf8(&value).ok().and_then(parse_schedstat));
            Some(Self {
                user_ticks,
                system_ticks,
                ticks_per_second,
                scheduler,
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            None
        }
    }

    pub(super) fn delta_since(self, earlier: Self) -> Option<ThreadCpuDelta> {
        Some(ThreadCpuDelta {
            user_ticks: self.user_ticks.checked_sub(earlier.user_ticks)?,
            system_ticks: self.system_ticks.checked_sub(earlier.system_ticks)?,
            ticks_per_second: match (self.ticks_per_second, earlier.ticks_per_second) {
                (Some(now), Some(before)) if now == before => Some(now),
                _ => None,
            },
            scheduler: match (self.scheduler, earlier.scheduler) {
                (Some(now), Some(before)) => Some(ThreadSchedulerDelta {
                    running_ns: now.running_ns.checked_sub(before.running_ns)?,
                    waiting_ns: now.waiting_ns.checked_sub(before.waiting_ns)?,
                    timeslices: now.timeslices.checked_sub(before.timeslices)?,
                }),
                _ => None,
            },
        })
    }
}

fn parse_thread_stat(stat: &str) -> Option<(u64, u64)> {
    // `comm` is parenthesized but may itself contain spaces and closing parentheses. The final
    // `)` is the delimiter before field 3 (state); utime/stime are fields 14/15.
    let close = stat.rfind(')')?;
    let fields: Vec<_> = stat.get(close + 1..)?.split_whitespace().collect();
    Some((fields.get(11)?.parse().ok()?, fields.get(12)?.parse().ok()?))
}

fn parse_ticks_per_second(value: &str) -> Option<u64> {
    value.parse::<u64>().ok().filter(|&ticks| ticks > 0)
}

fn parse_schedstat(value: &str) -> Option<ThreadSchedulerTime> {
    let mut fields = value.split_whitespace();
    Some(ThreadSchedulerTime {
        running_ns: fields.next()?.parse().ok()?,
        waiting_ns: fields.next()?.parse().ok()?,
        timeslices: fields.next()?.parse().ok()?,
    })
}

fn div_ceil(numerator: u128, denominator: u128) -> Option<u128> {
    if denominator == 0 {
        return None;
    }
    Some(numerator / denominator + u128::from(numerator % denominator != 0))
}

#[cfg(test)]
mod tests {
    use std::io;

    use super::{
        BLOCK_CELLS, DeadlineContract, ForecastBook, PhaseBudget, RunBudget, ThreadCpu,
        ThreadSchedulerTime, completed_block_upper_ns_per_cell, div_ceil,
        fork_and_report_projection, parse_schedstat, parse_thread_stat, parse_ticks_per_second,
        phase_summary_from_measurements, projection_fits,
    };

    fn empirical_report_input() -> String {
        format!(
            "source_sha256={}\ninput_sha256={}\nreport_variant=corrected-series-fixture\nmeasurements=16:20,32:50,64:150\ntarget_cells=231\nprojected_report_ns=2000\nforecast_description=external synthetic cost proposal with explicit prospective rational-bit-growth scope; empirical extrapolation only\nadequacy=empirical_forecast\ncheckpoint_reserve_ns=50\naa0_postwork_reserve_ns=100",
            "a".repeat(64),
            "b".repeat(64)
        )
    }

    #[test]
    fn empirical_growth_uses_the_smallest_exponent_covering_both_doublings() {
        let growth = super::empirical_report_growth_floor(16, 32, 64).unwrap();
        assert_eq!((growth.exponent, growth.floor_231_ns), (1, 231));
        assert_eq!(growth.measured_to_projected_ratio(231).unwrap(), (64, 231));
        assert!(growth.measured_to_projected_ratio(0).is_err());
        assert_eq!(
            super::empirical_report_growth_floor(10, 20, 40)
                .unwrap()
                .exponent,
            1
        );
        assert_eq!(
            super::empirical_report_growth_floor(10, 21, 40)
                .unwrap()
                .exponent,
            2
        );
        assert_eq!(
            super::empirical_report_growth_floor(10, 10, 21)
                .unwrap()
                .exponent,
            2
        );
        assert_eq!(
            super::empirical_report_growth_floor(1, 4, 16)
                .unwrap()
                .exponent,
            2
        );
        assert_eq!(
            super::empirical_report_growth_floor(1, 5, 16)
                .unwrap()
                .exponent,
            3
        );
        // Flat or decreasing timings retain the required e >= 1 floor.
        assert_eq!(
            super::empirical_report_growth_floor(3, 2, 1)
                .unwrap()
                .exponent,
            1
        );
    }

    #[test]
    fn empirical_growth_rounds_up_only_after_the_exact_power_ratio() {
        let rounded = super::empirical_report_growth_floor(20, 50, 150).unwrap();
        assert_eq!((rounded.exponent, rounded.floor_231_ns), (2, 1955));
        let integral = super::empirical_report_growth_floor(256, 1024, 4096).unwrap();
        assert_eq!((integral.exponent, integral.floor_231_ns), (2, 53_361));
        assert_eq!(
            super::empirical_report_growth_floor(1, 3, 4)
                .unwrap()
                .floor_231_ns,
            53
        );
    }

    #[test]
    fn empirical_growth_keeps_large_intermediates_and_refuses_only_unrepresentable_floor() {
        let timing = 1_u128 << 121;
        let growth = super::empirical_report_growth_floor(timing, timing, timing).unwrap();
        // timing*231 exceeds u128, while division by 64 gives this exact representable floor.
        assert_eq!(growth.floor_231_ns, 231_u128 << 115);
        let last = (u128::MAX / 231) * 64 + ((u128::MAX % 231) * 64) / 231;
        assert!(super::empirical_report_growth_floor(last, last, last).is_ok());
        assert!(super::empirical_report_growth_floor(last + 1, last + 1, last + 1).is_err());
        assert!(super::empirical_report_growth_floor(u128::MAX, u128::MAX, u128::MAX).is_err());
        assert!(super::empirical_report_growth_floor(1, u128::MAX, 1).is_err());
        for timings in [(0, 1, 1), (1, 0, 1), (1, 1, 0)] {
            assert!(super::empirical_report_growth_floor(timings.0, timings.1, timings.2).is_err());
        }
    }

    #[test]
    fn pinned_growth_proposal_must_cover_the_required_exact_empirical_floor() {
        let input = empirical_report_input();
        assert!(
            super::ReportAdmission::parse(
                &input.replace("projected_report_ns=2000", "projected_report_ns=1954")
            )
            .is_err()
        );
        let exact = super::ReportAdmission::parse(
            &input.replace("projected_report_ns=2000", "projected_report_ns=1955"),
        )
        .unwrap();
        assert_eq!(
            exact.empirical_growth.floor_231_ns,
            exact.projected_report_ns
        );
        assert_eq!(exact.empirical_growth.exponent, 2);
        assert!(
            super::ReportAdmission::parse(&input.replace(
                "measurements=16:20,32:50,64:150",
                "measurements=8:20,32:50,64:150"
            ))
            .is_err()
        );
    }

    #[test]
    fn fixed_phase_cap_stops_the_first_completed_block_above_its_admitted_rate() {
        let now = super::exterior_clock::monotonic_ns().unwrap();
        let run = RunBudget {
            deadline: DeadlineContract {
                started_ns: now,
                term_ns: now + 295_000_000_000,
                total_ns: now + 300_000_000_000,
                native_ns: now + 290_000_000_000,
            },
            reserve_ns: 0,
        };
        let mut phase = run
            .phase("synthetic admitted rate", 16, Some(160_000_000_000))
            .unwrap();
        for _ in 0..7 {
            phase.finish_cell(11_000_000_000).unwrap();
        }
        let error = phase.finish_cell(11_000_000_000).unwrap_err();
        assert!(error.to_string().contains("pre-admitted per-cell rate"));
        assert_eq!(phase.completed_cells, 8);
        assert!(
            phase.before_cell().is_err(),
            "a stopped phase must not start another cell"
        );
        assert_eq!(phase.phase_deadline_ns, phase.started_ns + 160_000_000_000);
    }

    #[test]
    fn admitted_block_rate_boundary_and_overflow_are_exact() {
        assert!(!super::completed_block_exceeds_admitted_rate(80, 160, 16));
        assert!(super::completed_block_exceeds_admitted_rate(81, 160, 16));
        assert!(!super::completed_block_exceeds_admitted_rate(
            u128::MAX,
            u128::MAX,
            8
        ));
        assert!(super::completed_block_exceeds_admitted_rate(
            u128::MAX,
            u128::MAX,
            9
        ));
    }

    #[test]
    fn cost_phase_ceilings_narrow_local_absolute_and_shared_time_without_extension() {
        let early = super::work_cutoff_at("report16", 100, 0, 30, 140, 285).unwrap();
        assert_eq!(early.deadline_ns, 130);
        let late = super::work_cutoff_at("report16", 120, 0, 30, 140, 285).unwrap();
        assert_eq!(late.deadline_ns, 140);
        assert!(late.check_at(139).is_ok());
        assert!(late.check_at(140).is_err());
        let shared = super::work_cutoff_at("later", 250, 0, 80, 340, 285).unwrap();
        assert_eq!(shared.deadline_ns, 285);
        assert!(super::work_cutoff_at("expired", 140, 0, 30, 140, 285).is_err());
        assert!(super::work_cutoff_at("overflow", u128::MAX - 1, 0, 30, 140, 285).is_err());
        assert!(super::work_cutoff_at("empty", 1, 0, 0, 140, 285).is_err());
    }

    #[test]
    fn raw_report_measurements_supply_no_population_growth_model() {
        let run = RunBudget {
            deadline: DeadlineContract {
                started_ns: 0,
                term_ns: u128::MAX,
                total_ns: u128::MAX,
                native_ns: u128::MAX,
            },
            reserve_ns: 0,
        };
        let mut report = super::ReportBudget::new(&run, "synthetic", 64);
        for _ in 0..8 {
            report.record_work(super::ReportWorkKind::HeldEval, 10);
        }
        report.record_work(super::ReportWorkKind::GramInverse, 20);
        report.record_work(super::ReportWorkKind::Other, 30);
        let summary = report.finish();
        assert_eq!(summary.held_eval.count, 8);
        assert_eq!(summary.held_eval.total_ns, 80);
        assert_eq!(summary.gram_inverse.total_ns, 20);
        assert_eq!(summary.other.total_ns, 30);
        assert_eq!(summary.projected_231_ns, None);
    }

    #[test]
    fn report_growth_input_refuses_missing_duplicate_and_uncertain_fields() {
        let input = empirical_report_input();
        assert!(super::ReportAdmission::parse("").is_err());
        assert!(
            super::ReportAdmission::parse(&input.replace("measurements=16:20,32:50,64:150\n", ""))
                .is_err()
        );
        assert!(
            super::ReportAdmission::parse(&format!("{input}\nprojected_report_ns=2000")).is_err()
        );
        assert!(super::ReportAdmission::parse(&format!("{input}\nunknown=1")).is_err());
        assert!(
            super::ReportAdmission::parse(
                &input.replace("adequacy=empirical_forecast", "adequacy=uncertain")
            )
            .is_err()
        );
        assert!(
            super::ReportAdmission::parse(&input.replace("target_cells=231", "target_cells=64"))
                .is_err()
        );
        assert!(
            super::ReportAdmission::parse(
                &input.replace("report_variant=corrected-series-fixture", "report_variant=")
            )
            .is_err()
        );
        assert!(
            super::ReportAdmission::parse(&input.replace(&"a".repeat(64), "unidentified-source"))
                .is_err()
        );
    }

    #[test]
    fn report_growth_requires_three_increasing_counts_and_positive_costs() {
        let input = empirical_report_input();
        for invalid in [
            "16:20,64:150",
            "16:20,16:50,64:150",
            "32:20,16:50,64:150",
            "0:20,32:50,64:150",
            "16:0,32:50,64:150",
            "16:-1,32:50,64:150",
            "16:20,32:50,232:150",
            "16:20,32:50,64:bad",
        ] {
            assert!(
                super::ReportAdmission::parse(&input.replace("16:20,32:50,64:150", invalid))
                    .is_err(),
                "{invalid}"
            );
        }
        // Timing monotonicity is neither required nor treated as a proof of future cost.
        assert!(
            super::ReportAdmission::parse(
                &input.replace("16:20,32:50,64:150", "16:50,32:20,64:60")
            )
            .is_ok()
        );
        for field in [
            "projected_report_ns",
            "checkpoint_reserve_ns",
            "aa0_postwork_reserve_ns",
        ] {
            let original = match field {
                "projected_report_ns" => 2000,
                "checkpoint_reserve_ns" => 50,
                _ => 100,
            };
            for invalid in ["0", "-1", "not-a-timing"] {
                assert!(
                    super::ReportAdmission::parse(&input.replace(
                        &format!("{field}={original}"),
                        &format!("{field}={invalid}")
                    ))
                    .is_err()
                );
            }
        }
        assert!(
            super::ReportAdmission::parse(
                &input.replace("projected_report_ns=2000", "projected_report_ns=149")
            )
            .is_err()
        );
    }

    #[test]
    fn report_admission_keeps_checkpoint_and_aa0_reserves_in_fixed_remaining_time() {
        let model = super::ReportAdmission::parse(&empirical_report_input()).unwrap();
        let admission = model.admit(200, 2, 4550, 2200).unwrap();
        assert_eq!(model.report_projection_ns(), 2000);
        assert_eq!(admission.one_branch_combined_ns, 2200);
        assert_eq!(admission.fork_horizon_ns, 4400);
        assert_eq!(admission.total_required_ns, 4550);
        assert!(model.admit(200, 2, 4549, 2200).is_err());
        assert!(model.admit(200, 2, 4550, 2199).is_err());
        assert!(model.admit(200, 0, u128::MAX, u128::MAX).is_err());
        // After actual checkpoint time is deducted, only the already spent reserve is omitted.
        assert_eq!(
            model
                .admit_after_checkpoint(200, 2, 4500, 2200)
                .unwrap()
                .total_required_ns,
            4500
        );
        assert!(model.admit_after_checkpoint(200, 2, 4499, 2200).is_err());
        assert!(model.admit(200, 2, 100, 2200).is_err());
    }

    #[test]
    fn report_admission_refuses_overflow_in_cost_horizon_and_reserve_series() {
        let input = empirical_report_input();
        assert!(
            super::ReportAdmission::parse(&input.replace(
                "projected_report_ns=2000",
                &format!("projected_report_ns={}", u128::MAX)
            ))
            .is_err()
        );
        let model = super::ReportAdmission::parse(&input).unwrap();
        assert!(model.admit(u128::MAX, 1, u128::MAX, u128::MAX).is_err());
        assert!(model.admit(u128::MAX / 2, 3, u128::MAX, u128::MAX).is_err());
        assert!(!projection_fits(u128::MAX, 1, 1, u128::MAX, u128::MAX));
        assert!(!projection_fits(u128::MAX / 2, 0, 3, u128::MAX, u128::MAX));
        assert!(!projection_fits(1, 1, 0, u128::MAX, u128::MAX));
    }

    #[test]
    fn exact_mean_plus_spread_uses_rational_fixed_block_rates() {
        let mut forecast = ForecastBook::default();
        forecast.push(80); // 10 ns/cell
        forecast.push(160); // 20 ns/cell
        let f = forecast.snapshot().expect("two blocks produce a forecast");
        assert_eq!((f.mean_numerator_ns, f.mean_denominator), (240, 16));
        assert_eq!((f.spread_numerator_ns, f.spread_denominator), (80, 8));
        assert_eq!(f.upper_ns_per_cell, 25); // ceil(15 + 10)
    }

    #[test]
    fn isolated_spike_is_not_a_single_cell_abort_or_second_block_stop() {
        let mut forecast = ForecastBook::default();
        // Seven ordinary timings and one spike make a completed block rate of 21.25 ns/cell.
        let block = [10_u128, 10, 10, 10, 10, 10, 10, 100]
            .into_iter()
            .sum::<u128>();
        forecast.push(block);
        assert_eq!(BLOCK_CELLS, 8);
        assert_eq!(forecast.upper_ns_per_cell(), Some(22)); // ceil(170 / 8)
        let projected_ns = 1_000 + forecast.upper_ns_per_cell().unwrap() * 10;
        let allowed_ns = 1_200;
        let bad_blocks = usize::from(projected_ns > allowed_ns);
        assert_eq!(bad_blocks, 1); // warning only; two sustained completed blocks are required
    }

    #[test]
    fn completed_block_forecast_aggregates_spike_and_ignores_incomplete_tail() {
        let mut cell_times = vec![10_u128; 7];
        cell_times.push(100); // one slow cell contributes to its completed block, not a hard cap
        cell_times.extend([10_u128; 8]);
        cell_times.push(u128::MAX); // incomplete tail is not admitted into the forecast
        // M=250/16 and S=90/8, so ceil(M+S)=ceil(26.875)=27.
        assert_eq!(completed_block_upper_ns_per_cell(&cell_times), Some(27));
        assert_eq!(completed_block_upper_ns_per_cell(&[u128::MAX]), None);
    }

    #[test]
    fn projection_warning_recovers_after_a_good_completed_block() {
        let mut forecast = ForecastBook::default();
        forecast.push(800);
        let first_projected = 1_000 + forecast.upper_ns_per_cell().unwrap() * 20;
        let allowed_ns = 2_500;
        let mut streak = usize::from(first_projected > allowed_ns);
        assert_eq!(streak, 1);
        forecast.push(80);
        let recovered_projected = 2_000 + forecast.upper_ns_per_cell().unwrap() * 2;
        streak = if recovered_projected > allowed_ns {
            streak + 1
        } else {
            0
        };
        assert_eq!(streak, 0);
    }

    #[test]
    fn sustained_projected_exhaustion_stops_after_two_completed_blocks() {
        let mut forecast = ForecastBook::default();
        let mut streak = 0;
        for block in [800, 800] {
            forecast.push(block);
            let projected = 1_000 + forecast.upper_ns_per_cell().unwrap() * 20;
            streak = if projected > 2_500 { streak + 1 } else { 0 };
        }
        assert_eq!(streak, 2);
    }

    #[test]
    fn next_declared_unit_must_fit_before_waiting_for_another_window() {
        let forecast_upper = 25;
        let phase_left = 25;
        let global_left = 100;
        let fits_next_unit = phase_left > forecast_upper && global_left > forecast_upper;
        assert!(!fits_next_unit);
    }

    #[test]
    fn fixed_deadline_reserve_and_external_caps_are_not_forecast_inputs() {
        let mut forecast = ForecastBook::default();
        forecast.push(8_000);
        let projected = 1_000 + forecast.upper_ns_per_cell().unwrap() * 10;
        let phase_allowance = 100_000; // fixed at phase entry; never raised by the forecast
        assert!(projected <= phase_allowance);
        let externally_enforced_rss_cap_bytes = 8_u128 * 1024 * 1024 * 1024;
        assert_eq!(externally_enforced_rss_cap_bytes, 8_589_934_592);
    }

    #[test]
    fn fork_admission_includes_concurrent_report_projection() {
        let native_per_branch = 80_u128;
        let report_per_branch = 30_u128;
        let waves: usize = 1;
        let remaining = 100_u128;
        assert!(native_per_branch * waves as u128 <= remaining);
        assert_eq!(
            fork_and_report_projection(native_per_branch, report_per_branch, waves),
            110
        );
        assert!(!projection_fits(
            native_per_branch,
            report_per_branch,
            waves,
            remaining,
            180
        ));
        assert!(projection_fits(70, 30, 1, 100, 100));
        assert!(!projection_fits(70, 30, 1, 99, 100));
        assert!(projection_fits(30, 10, 2, 80, 40));
        assert!(!projection_fits(30, 10, 2, 79, 40));
    }

    #[test]
    fn parser_reads_linux_thread_cpu_ticks_and_optional_schedstat() {
        // field 3 begins after the final ')' in comm. utime/stime are stat fields 14 and 15.
        let stat = "123 (thread name ) with parens) S 1 2 3 4 5 6 7 8 9 10 110 12 13";
        assert_eq!(parse_thread_stat(stat), Some((110, 12)));
        assert_eq!(
            parse_schedstat("1000 250 7\n"),
            Some(super::ThreadSchedulerTime {
                running_ns: 1000,
                waiting_ns: 250,
                timeslices: 7,
            })
        );
        assert_eq!(parse_schedstat("1000 nope 7"), None);
    }

    #[test]
    fn cpu_delta_preserves_resolution_and_separates_scheduler_counters() {
        let before = ThreadCpu {
            user_ticks: 100,
            system_ticks: 20,
            ticks_per_second: Some(100),
            scheduler: Some(ThreadSchedulerTime {
                running_ns: 1_000,
                waiting_ns: 500,
                timeslices: 8,
            }),
        };
        let after = ThreadCpu {
            user_ticks: 107,
            system_ticks: 23,
            ticks_per_second: Some(100),
            scheduler: Some(ThreadSchedulerTime {
                running_ns: 2_000,
                waiting_ns: 800,
                timeslices: 10,
            }),
        };
        let delta = after.delta_since(before).expect("monotone counters");
        assert_eq!((delta.user_ticks, delta.system_ticks), (7, 3));
        assert_eq!(delta.ticks_per_second, Some(100));
        assert_eq!(
            delta.scheduler,
            Some(super::ThreadSchedulerDelta {
                running_ns: 1_000,
                waiting_ns: 300,
                timeslices: 2,
            })
        );
        assert_eq!(parse_ticks_per_second("100"), Some(100));
        assert_eq!(parse_ticks_per_second("0"), None);
        assert_eq!(parse_ticks_per_second("unknown"), None);
        assert_eq!(
            after
                .delta_since(ThreadCpu {
                    ticks_per_second: Some(250),
                    ..before
                })
                .expect("ticks still differ monotonically")
                .ticks_per_second,
            None
        );
    }

    #[test]
    fn partial_stop_summary_keeps_reason_count_measured_rate_and_projection() {
        let summary = phase_summary_from_measurements(
            "synthetic".to_owned(),
            5,
            9,
            100,
            250,
            1_000,
            Some(75),
            1,
            Some("next unit cannot fit".to_owned()),
        );
        assert!(summary.incomplete);
        assert_eq!(summary.stop_reason.as_deref(), Some("next unit cannot fit"));
        assert_eq!((summary.completed_cells, summary.declared_cells), (5, 9));
        assert_eq!(summary.measured_cell_wall_ns, 250);
        assert_eq!(summary.forecast_upper_ns_per_cell, Some(75));
        assert_eq!(summary.projected_ns, Some(400));
    }

    #[test]
    fn expired_before_cell_error_drops_incomplete_partial_block_summary() {
        let now = super::exterior_clock::monotonic_ns().expect("Linux monotonic clock");
        let mut forecast = ForecastBook::default();
        forecast.push(80);
        forecast.push(160);
        let mut phase = PhaseBudget {
            label: "expired synthetic phase".to_owned(),
            started_ns: now,
            last_clock_ns: now,
            phase_deadline_ns: 0,
            deadline: DeadlineContract {
                started_ns: 0,
                term_ns: 0,
                total_ns: 0,
                native_ns: 0,
            },
            reserve_ns: 0,
            total_cells: 9,
            completed_cells: 5,
            measured_cell_wall_ns: 250,
            block_cells: 5,
            block_wall_ns: 250,
            block_index: 0,
            forecast,
            consecutive_bad_blocks: 0,
            phase_allowance_ns: 1_000,
            explicit_phase_cap: false,
            stop_reason: None,
            summary_written: false,
        };

        let error = phase.before_cell().expect_err("expired absolute cutoff");
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        let summary = phase.summary();
        assert!(summary.incomplete);
        assert!(
            summary
                .stop_reason
                .as_deref()
                .expect("before_cell records its stop")
                .contains("fixed native/phase cutoff reached")
        );
        assert_eq!((summary.completed_cells, summary.declared_cells), (5, 9));
        assert_eq!(summary.measured_cell_wall_ns, 250);
        assert_eq!(summary.forecast_upper_ns_per_cell, Some(25));
        assert_eq!(summary.projected_ns, Some(summary.elapsed_wall_ns + 25 * 4));
        assert_eq!((phase.block_cells, phase.block_wall_ns), (5, 250));

        // Dropping the real tracker exercises the fallback writer for the partial block and
        // incomplete phase receipt, rather than only testing the summary value constructor.
        drop(phase);
    }

    #[test]
    fn later_phase_start_stays_bounded_by_shared_absolute_cutoff() {
        let now = super::exterior_clock::monotonic_ns().expect("Linux monotonic clock");
        let native_cutoff = now + 290_000_000_000;
        let reserve_ns = 100;
        let budget = RunBudget {
            deadline: DeadlineContract {
                started_ns: now,
                term_ns: now + 295_000_000_000,
                total_ns: now + 300_000_000_000,
                native_ns: native_cutoff,
            },
            reserve_ns,
        };
        let before_phase = budget.remaining_ns().expect("shared cutoff budget");
        let phase = budget
            .phase("later local phase", 1, None)
            .expect("cutoff remains available");
        let after_phase_start = budget.remaining_ns().expect("same shared cutoff");

        assert!(after_phase_start <= before_phase);
        assert_eq!(phase.phase_deadline_ns, native_cutoff - reserve_ns);
        assert!(phase.phase_deadline_ns <= native_cutoff - reserve_ns);
        drop(phase);
    }

    #[test]
    fn ceil_and_invalid_zero_denominator_are_exact() {
        assert_eq!(div_ceil(10, 4), Some(3));
        assert_eq!(div_ceil(8, 4), Some(2));
        assert_eq!(div_ceil(1, 0), None);
    }
}
