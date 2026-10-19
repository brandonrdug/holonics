//! Fixed-deadline timing and process-local observability for the step-0 diagnostic.
//!
//! The native phase uses the supervisor's Linux `CLOCK_MONOTONIC` deadlines. It reserves the
//! declared postwork interval inside the native cutoff; it cannot create or extend a deadline.

#[path = "exterior_clock.rs"]
mod exterior_clock;

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

impl RunBudget {
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
    measured_cells: usize,
    started: Instant,
    held_eval: Vec<u128>,
    gram_inverse: Vec<u128>,
    other: Vec<u128>,
}

impl ReportBudget {
    pub(super) fn new(run: &RunBudget, branch: &str, measured_cells: usize) -> Self {
        Self {
            run: run.clone(),
            branch: branch.to_owned(),
            measured_cells,
            started: Instant::now(),
            held_eval: Vec::new(),
            gram_inverse: Vec::new(),
            other: Vec::new(),
        }
    }

    pub(super) fn check_before_work(&self, label: &str) -> io::Result<()> {
        if self.run.remaining_report_ns()? == 0 {
            return Err(timed_out(format!(
                "branch {} cannot start {label}: the shared 285-second phase cutoff was reached (five-second report floor)",
                self.branch
            )));
        }
        Ok(())
    }

    pub(super) fn remaining_ns(&self) -> io::Result<u128> {
        self.run.remaining_report_ns()
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
        let held_upper = completed_block_upper_ns_per_cell(&self.held_eval);
        let projected_held = held_upper.map(|per_eval| per_eval.saturating_mul(3 * 231));
        let projected_inverse = (gram_inverse.count > 0).then_some(gram_inverse.max_ns);
        let projected_other =
            (other.count > 0).then(|| project_other_to_231(other.total_ns, self.measured_cells));
        let projected_231_ns = projected_held
            .zip(projected_inverse)
            .zip(projected_other)
            .map(|((held, inverse), other)| held.saturating_add(inverse).saturating_add(other));
        let remaining_report_ns = self.run.remaining_report_ns().unwrap_or(0);
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

fn project_other_to_231(other_ns: u128, measured_cells: usize) -> u128 {
    if measured_cells == 0 {
        return u128::MAX;
    }
    div_ceil(other_ns.saturating_mul(231), measured_cells as u128).unwrap_or(u128::MAX)
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
    native_per_branch_ns.saturating_add(report_per_branch_ns) <= branch_cap_ns
        && fork_and_report_projection(native_per_branch_ns, report_per_branch_ns, branch_waves)
            <= remaining_phase_ns
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
    stop_reason: Option<String>,
    summary_written: bool,
}

impl PhaseBudget {
    /// Check actual native/phase time and whether the latest completed-block upper estimate can
    /// fit the next declared unit. Call before starting that unit.
    pub(super) fn before_cell(&mut self) -> io::Result<()> {
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
    /// Complete eight-cell blocks update forecasts; the final partial block is reported separately.
    pub(super) fn finish_cell(&mut self, cell_ns: u128) -> io::Result<()> {
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
            self.report_block(false);
            self.block_cells = 0;
            self.block_wall_ns = 0;
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
        phase_summary_from_measurements, project_other_to_231, projection_fits,
    };

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
    fn report_other_projection_uses_actual_calibration_cell_count() {
        assert_eq!(project_other_to_231(64, 64), 231);
        assert_eq!(project_other_to_231(231, 231), 231);
        assert_eq!(project_other_to_231(64, 0), u128::MAX);
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
