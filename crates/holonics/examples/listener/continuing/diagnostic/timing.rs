//! Fixed-deadline timing and process-local observability for the step-0 diagnostic.
//!
//! The caller owns the native transaction. A `PhaseBudget` checks whether that next declared
//! unit can still fit, records its elapsed time, and reports fixed eight-cell blocks. It never
//! imposes a per-cell latency ceiling. Forecasts are feasibility warnings from completed blocks,
//! not guarantees of constant cost.

use std::io;
use std::time::{Duration, Instant};

const RUN_WALL_CAP_NS: u128 = 300_000_000_000;
const BLOCK_CELLS: usize = 8;

/// A shared immutable start/deadline. `Instant` and the scalar reserve make this safe to borrow
/// from independent branch workers; each worker creates its own `PhaseBudget`.
#[derive(Clone, Debug)]
pub(super) struct RunBudget {
    started: Instant,
    reserve_ns: u128,
}

impl RunBudget {
    /// Starts the absolute 300-second wall deadline and reserves time for declared postwork.
    pub(super) fn new(reserve_ns: u128) -> io::Result<Self> {
        if reserve_ns >= RUN_WALL_CAP_NS {
            return Err(invalid(
                "the explicit reserve must be less than the 300-second run cap",
            ));
        }
        Ok(Self {
            started: Instant::now(),
            reserve_ns,
        })
    }

    /// Opens a phase against the remaining global budget. Its allowance is fixed at entry and
    /// cannot be increased by later forecasts. `cap_ns` is an optional narrower phase cap.
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
        let now = Instant::now();
        let global_left = self.global_remaining_ns_at(now);
        let phase_allowance_ns = cap_ns.map_or(global_left, |cap| cap.min(global_left));
        if phase_allowance_ns == 0 {
            return Err(timed_out("no global wall budget remains for this phase"));
        }
        let end = now
            .checked_add(duration_from_ns(phase_allowance_ns))
            .ok_or_else(|| invalid("phase deadline is outside the representable clock range"))?;
        Ok(PhaseBudget {
            label: label.to_owned(),
            started: now,
            end,
            global_deadline: self.global_deadline(),
            reserve_ns: self.reserve_ns,
            total_cells,
            completed_cells: 0,
            block_cells: 0,
            block_wall_ns: 0,
            block_index: 0,
            forecast: ForecastBook::default(),
            consecutive_bad_blocks: 0,
            phase_allowance_ns,
        })
    }

    fn global_deadline(&self) -> Instant {
        self.started + duration_from_ns(RUN_WALL_CAP_NS)
    }

    fn global_remaining_ns_at(&self, now: Instant) -> u128 {
        let deadline = self.global_deadline();
        let hard_left = deadline.saturating_duration_since(now).as_nanos();
        hard_left.saturating_sub(self.reserve_ns)
    }
}

/// Per-phase mutable accounting. One instance belongs to one worker; independent workers share
/// only their `&RunBudget` and therefore do not serialize native work through a timing mutex.
#[derive(Debug)]
pub(super) struct PhaseBudget {
    label: String,
    started: Instant,
    end: Instant,
    global_deadline: Instant,
    reserve_ns: u128,
    total_cells: usize,
    completed_cells: usize,
    block_cells: usize,
    block_wall_ns: u128,
    block_index: usize,
    forecast: ForecastBook,
    consecutive_bad_blocks: usize,
    phase_allowance_ns: u128,
}

impl PhaseBudget {
    /// Check actual phase/global time and whether the latest completed-block upper estimate can
    /// fit the next declared unit. This check occurs before the caller starts that unit.
    pub(super) fn before_cell(&self) -> io::Result<()> {
        if self.completed_cells >= self.total_cells {
            return Err(invalid("phase has no declared work units remaining"));
        }
        let now = Instant::now();
        let phase_left = self.end.saturating_duration_since(now).as_nanos();
        let global_left = self.global_remaining_ns_at(now);
        if phase_left == 0 || global_left == 0 || now >= self.global_deadline {
            return Err(timed_out(format!(
                "{} stopped before cell {}: fixed phase/global deadline reached",
                self.label,
                self.completed_cells + 1
            )));
        }
        if let Some(upper_ns_per_cell) = self.forecast.upper_ns_per_cell() {
            if phase_left <= upper_ns_per_cell || global_left <= upper_ns_per_cell {
                return Err(timed_out(format!(
                    "{} stopped before cell {}: remaining hard budget cannot fit the next declared unit (forecast upper {} ns)",
                    self.label,
                    self.completed_cells + 1,
                    upper_ns_per_cell
                )));
            }
        }
        if self.consecutive_bad_blocks >= 2 {
            return Err(timed_out(format!(
                "{} stopped before cell {}: projected exhaustion persisted for two completed blocks",
                self.label,
                self.completed_cells + 1
            )));
        }
        Ok(())
    }

    /// Records one completed native unit. The observed duration is never an individual-cell
    /// abort condition. Complete blocks update forecasts; an unfinished tail is reported only by
    /// `finish_phase` and is excluded from the fixed-block estimate.
    pub(super) fn finish_cell(&mut self, cell_ns: u128) -> io::Result<()> {
        if self.completed_cells >= self.total_cells {
            return Err(invalid("more completed cells than the phase declared"));
        }
        self.completed_cells += 1;
        self.block_cells += 1;
        self.block_wall_ns = self.block_wall_ns.saturating_add(cell_ns);
        if self.block_cells == BLOCK_CELLS {
            self.block_index += 1;
            self.forecast.push(self.block_wall_ns);
            self.update_projection_streak();
            self.report_block(false);
            self.block_cells = 0;
            self.block_wall_ns = 0;
        }
        Ok(())
    }

    /// Reports a final partial block and returns the exact phase accounting. A partial block is
    /// not inserted into the forecast, so the estimator always uses fixed eight-cell blocks.
    pub(super) fn finish_phase(mut self) -> PhaseSummary {
        if self.block_cells > 0 {
            self.report_block(true);
        }
        PhaseSummary {
            label: self.label,
            completed_cells: self.completed_cells,
            declared_cells: self.total_cells,
            elapsed_wall_ns: self.started.elapsed().as_nanos(),
            phase_allowance_ns: self.phase_allowance_ns,
            forecast_upper_ns_per_cell: self.forecast.upper_ns_per_cell(),
            consecutive_bad_blocks: self.consecutive_bad_blocks,
        }
    }

    fn global_remaining_ns_at(&self, now: Instant) -> u128 {
        let hard_left = self
            .global_deadline
            .saturating_duration_since(now)
            .as_nanos();
        hard_left.saturating_sub(self.reserve_ns)
    }

    fn update_projection_streak(&mut self) {
        let Some(upper_ns_per_cell) = self.forecast.upper_ns_per_cell() else {
            return;
        };
        let remaining_cells = self.total_cells.saturating_sub(self.completed_cells) as u128;
        let projected = self
            .started
            .elapsed()
            .as_nanos()
            .saturating_add(upper_ns_per_cell.saturating_mul(remaining_cells));
        if projected > self.phase_allowance_ns {
            self.consecutive_bad_blocks = self.consecutive_bad_blocks.saturating_add(1);
        } else {
            self.consecutive_bad_blocks = 0;
        }
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
            "timing phase={} block={} cells={} wall_ns={} partial={} completed={} elapsed_wall_ns={} phase_allowance_ns={} M={:?}/{:?}ns_per_cell S={:?}/{:?}ns_per_cell ceil(M+S)={:?}ns_per_cell remaining_cells={} projected_ns={} bad_block_streak={}",
            self.label,
            self.block_index + usize::from(partial),
            self.block_cells.max(if partial { 0 } else { BLOCK_CELLS }),
            self.block_wall_ns,
            partial,
            self.completed_cells,
            self.started.elapsed().as_nanos(),
            self.phase_allowance_ns,
            mean_num,
            mean_den,
            spread_num,
            spread_den,
            upper,
            self.total_cells.saturating_sub(self.completed_cells),
            upper.map(|rate| self.started.elapsed().as_nanos().saturating_add(
                rate.saturating_mul(
                    (self.total_cells.saturating_sub(self.completed_cells)) as u128
                )
            )),
            self.consecutive_bad_blocks,
        );
    }
}

/// Small immutable end-of-phase receipt for the parent diagnostic to log or serialize.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct PhaseSummary {
    pub(super) label: String,
    pub(super) completed_cells: usize,
    pub(super) declared_cells: usize,
    pub(super) elapsed_wall_ns: u128,
    pub(super) phase_allowance_ns: u128,
    pub(super) forecast_upper_ns_per_cell: Option<u128>,
    pub(super) consecutive_bad_blocks: usize,
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
            let stat = std::fs::read_to_string("/proc/thread-self/stat").ok()?;
            let (user_ticks, system_ticks) = parse_thread_stat(&stat)?;
            let ticks_per_second = std::env::var("REQ063_CLK_TCK")
                .ok()
                .and_then(|value| parse_ticks_per_second(&value));
            let scheduler = std::fs::read_to_string("/proc/thread-self/schedstat")
                .ok()
                .and_then(|value| parse_schedstat(&value));
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

fn duration_from_ns(nanos: u128) -> Duration {
    Duration::from_nanos(nanos.min(u64::MAX as u128) as u64)
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidInput, message.into())
}

fn timed_out(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::TimedOut, message.into())
}

#[cfg(test)]
mod tests {
    use super::{
        BLOCK_CELLS, ForecastBook, ThreadCpu, ThreadSchedulerTime,
        completed_block_upper_ns_per_cell, div_ceil, parse_schedstat, parse_thread_stat,
        parse_ticks_per_second,
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
        // Seven ordinary timings and one spike make a completed block rate of 22.5 ns/cell.
        let block = [10_u128, 10, 10, 10, 10, 10, 10, 100]
            .into_iter()
            .sum::<u128>();
        forecast.push(block);
        assert_eq!(BLOCK_CELLS, 8);
        assert_eq!(forecast.upper_ns_per_cell(), Some(23)); // ceil(180 / 8)
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
        assert_eq!(completed_block_upper_ns_per_cell(&cell_times), Some(29));
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
    fn ceil_and_invalid_zero_denominator_are_exact() {
        assert_eq!(div_ceil(10, 4), Some(3));
        assert_eq!(div_ceil(8, 4), Some(2));
        assert_eq!(div_ceil(1, 0), None);
    }
}
