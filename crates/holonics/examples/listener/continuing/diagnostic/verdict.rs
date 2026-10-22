//! Deferred scientific verdicts for diagnostics that still have bounded readouts to collect.

use super::Result;

/// Retain a branch's scientific failure while allowing separately budgeted readouts to finish.
pub(super) fn defer_report_result(
    branch: &str,
    result: std::result::Result<(), String>,
    failures: &mut Vec<String>,
) {
    if let Err(error) = result {
        let message = format!("branch={branch} {error}");
        println!("step0_epoch_report_deferred_failure {message}");
        failures.push(message);
    }
}

/// Return a failure only after all deferred diagnostic readouts have been collected.
pub(super) fn finish_deferred_reports(failures: &[String]) -> Result<()> {
    if failures.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "diagnostic scientific reports failed ({}): {}",
            failures.len(),
            failures.join("; ")
        )
        .into())
    }
}

#[cfg(test)]
mod tests {
    use super::super::execution::one_thread_pool;
    use super::super::timing::projection_fits;
    use super::{defer_report_result, finish_deferred_reports};
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[test]
    fn failed_calibration_is_deferred_until_admitted_fork_readouts_finish() {
        let mut failures = Vec::new();
        defer_report_result(
            "calibration",
            Err("scientific verdict mismatch".to_owned()),
            &mut failures,
        );
        assert_eq!(failures.len(), 1);
        assert!(failures[0].contains("branch=calibration"));

        let callback_count = AtomicUsize::new(0);
        let admitted = projection_fits(70, 30, 1, 100, 100);
        assert!(admitted, "the synthetic fork fits the declared projection");
        if admitted {
            let pool = one_thread_pool().expect("bounded synthetic pool builds");
            pool.install(|| {
                callback_count.fetch_add(1, Ordering::Relaxed);
            });
        }
        assert_eq!(callback_count.load(Ordering::Relaxed), 1);

        let final_status = finish_deferred_reports(&failures);
        assert!(
            final_status.is_err(),
            "a retained verdict prevents completion"
        );
    }

    #[test]
    fn timing_refusal_skips_fork_and_no_failures_can_complete() {
        let callback_count = AtomicUsize::new(0);
        let admitted = projection_fits(70, 30, 1, 99, 100);
        assert!(!admitted, "the synthetic fork exceeds remaining phase time");
        if admitted {
            let pool = one_thread_pool().expect("bounded synthetic pool builds");
            pool.install(|| {
                callback_count.fetch_add(1, Ordering::Relaxed);
            });
        }
        assert_eq!(callback_count.load(Ordering::Relaxed), 0);
        assert!(finish_deferred_reports(&[]).is_ok());
    }
}
