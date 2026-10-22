//! Exterior executor setup for the listener diagnostic's independent branches.

use super::Result;

/// Build a dedicated one-worker Rayon pool for one diagnostic branch or calibration.
pub(super) fn one_thread_pool() -> Result<rayon::ThreadPool> {
    Ok(rayon::ThreadPoolBuilder::new().num_threads(1).build()?)
}

#[cfg(test)]
mod tests {
    use super::one_thread_pool;
    use rayon::prelude::*;
    use std::collections::HashSet;
    use std::thread::ThreadId;

    fn nested_worker_observations(
        pool: &rayon::ThreadPool,
    ) -> Vec<(usize, ThreadId, usize, Option<usize>)> {
        pool.install(|| {
            (0..8usize)
                .into_par_iter()
                .map(|cell| {
                    (
                        cell,
                        std::thread::current().id(),
                        rayon::current_num_threads(),
                        rayon::current_thread_index(),
                    )
                })
                .collect()
        })
    }

    #[test]
    fn diagnostic_branches_and_calibration_use_distinct_single_worker_pools() {
        let branch_pools = [
            one_thread_pool().expect("first branch pool builds"),
            one_thread_pool().expect("second branch pool builds"),
            one_thread_pool().expect("third branch pool builds"),
        ];
        let calibration_pool = one_thread_pool().expect("calibration pool builds");

        let branch_observations: Vec<_> = branch_pools
            .iter()
            .map(nested_worker_observations)
            .collect();
        let branch_ids: HashSet<_> = branch_observations
            .iter()
            .map(|observations| observations[0].1.clone())
            .collect();
        assert_eq!(branch_ids.len(), branch_pools.len());
        for observations in &branch_observations {
            assert_eq!(observations.len(), 8);
            let worker_id = &observations[0].1;
            for (_, observed_id, worker_count, worker_index) in observations {
                assert_eq!(observed_id, worker_id);
                assert_eq!(*worker_count, 1);
                assert_eq!(*worker_index, Some(0));
            }
        }

        let calibration_observations = nested_worker_observations(&calibration_pool);
        assert_eq!(calibration_observations.len(), 8);
        let calibration_worker = &calibration_observations[0].1;
        assert!(!branch_ids.contains(calibration_worker));
        for (_, observed_id, worker_count, worker_index) in &calibration_observations {
            assert_eq!(observed_id, calibration_worker);
            assert_eq!(*worker_count, 1);
            assert_eq!(*worker_index, Some(0));
        }
    }
}
