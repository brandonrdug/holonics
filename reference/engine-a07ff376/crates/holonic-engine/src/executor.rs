//! Deterministic physical realization on CPU cores.
//!
//! Causal antichains and receiver-local apertures may be realized in parallel.
//! Worker scheduling never becomes chronology: every result returns in the
//! canonical input address order.

use std::num::NonZeroUsize;

use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CpuExecutionMode {
    Serial,
    Multicore { workers: NonZeroUsize },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuExecutor {
    pub mode: CpuExecutionMode,
}

impl CpuExecutor {
    pub const fn serial() -> Self {
        Self {
            mode: CpuExecutionMode::Serial,
        }
    }

    pub const fn multicore(workers: NonZeroUsize) -> Self {
        Self {
            mode: CpuExecutionMode::Multicore { workers },
        }
    }

    pub fn execute_indexed<T, R, E>(
        &self,
        inputs: &[T],
        operation: impl Fn(usize, &T) -> Result<R, E> + Sync,
    ) -> Result<(Vec<R>, CpuExecutionReceipt), CpuExecutionError<E>>
    where
        T: Sync,
        R: Send,
        E: Send,
    {
        match self.mode {
            CpuExecutionMode::Serial => {
                let outputs = inputs
                    .iter()
                    .enumerate()
                    .map(|(index, input)| {
                        operation(index, input).map_err(CpuExecutionError::Operation)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((
                    outputs,
                    CpuExecutionReceipt {
                        schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
                        mode: "serial".to_owned(),
                        tasks: BigUint::from(inputs.len()),
                        worker_limit: BigUint::from(1_u8),
                        workers_used: BigUint::from((!inputs.is_empty()) as u8),
                        batches: BigUint::from((!inputs.is_empty()) as u8),
                        joins: BigUint::from(0_u8),
                    },
                ))
            }
            CpuExecutionMode::Multicore { workers } => {
                if inputs.is_empty() {
                    return Ok((
                        Vec::new(),
                        CpuExecutionReceipt {
                            schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
                            mode: "multicore".to_owned(),
                            tasks: BigUint::from(0_u8),
                            worker_limit: BigUint::from(workers.get()),
                            workers_used: BigUint::from(0_u8),
                            batches: BigUint::from(0_u8),
                            joins: BigUint::from(0_u8),
                        },
                    ));
                }
                let workers_used = workers.get().min(inputs.len());
                let mut indexed = std::thread::scope(|scope| {
                    let quotient = inputs.len() / workers_used;
                    let remainder = inputs.len() % workers_used;
                    let handles = (0..workers_used)
                        .map(|worker| {
                            let first = worker * quotient + worker.min(remainder);
                            let count = quotient + usize::from(worker < remainder);
                            let chunk = &inputs[first..first + count];
                            let operation = &operation;
                            scope.spawn(move || {
                                chunk
                                    .iter()
                                    .enumerate()
                                    .map(|(offset, input)| {
                                        let index = first + offset;
                                        operation(index, input).map(|output| (index, output))
                                    })
                                    .collect::<Result<Vec<_>, E>>()
                            })
                        })
                        .collect::<Vec<_>>();
                    let mut indexed = Vec::with_capacity(inputs.len());
                    for handle in handles {
                        let batch = handle
                            .join()
                            .map_err(|_| CpuExecutionError::WorkerPanicked)?
                            .map_err(CpuExecutionError::Operation)?;
                        indexed.extend(batch);
                    }
                    Ok::<_, CpuExecutionError<E>>(indexed)
                })?;
                indexed.sort_by_key(|(index, _)| *index);
                Ok((
                    indexed.into_iter().map(|(_, output)| output).collect(),
                    CpuExecutionReceipt {
                        schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
                        mode: "multicore".to_owned(),
                        tasks: BigUint::from(inputs.len()),
                        worker_limit: BigUint::from(workers.get()),
                        workers_used: BigUint::from(workers_used),
                        batches: BigUint::from(workers_used),
                        joins: BigUint::from(workers_used),
                    },
                ))
            }
        }
    }

    /// Realize two independent, heterogeneous apparatus currents over the same predecessor.
    /// Their return address is fixed as `(left, right)`; worker completion order is not exposed.
    /// This is the physical owner for port-level overlap and prevents application conductors from
    /// manufacturing their own host-thread choreography.
    pub fn execute_independent_pair<L, R>(
        &self,
        left: impl FnOnce() -> L + Send,
        right: impl FnOnce() -> R,
    ) -> Result<(L, R, CpuExecutionReceipt), CpuExecutionError<std::convert::Infallible>>
    where
        L: Send,
    {
        let configured_workers = match self.mode {
            CpuExecutionMode::Serial => 1,
            CpuExecutionMode::Multicore { workers } => workers.get(),
        };
        if configured_workers < 2 {
            return Ok((
                left(),
                right(),
                CpuExecutionReceipt {
                    schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
                    mode: "serial".to_owned(),
                    tasks: BigUint::from(2_u8),
                    worker_limit: BigUint::from(1_u8),
                    workers_used: BigUint::from(1_u8),
                    batches: BigUint::from(1_u8),
                    joins: BigUint::from(0_u8),
                },
            ));
        }
        let (left, right) = std::thread::scope(|scope| {
            let left = scope.spawn(left);
            // Resident apparatus such as a native card handle is physically bound to the
            // mounting thread. Run that current here while the transferable current occupies
            // the independent worker; the application never moves or re-mounts the apparatus.
            let right = right();
            let left = left.join().map_err(|_| CpuExecutionError::WorkerPanicked)?;
            Ok::<_, CpuExecutionError<std::convert::Infallible>>((left, right))
        })?;
        Ok((
            left,
            right,
            CpuExecutionReceipt {
                schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
                mode: "multicore".to_owned(),
                tasks: BigUint::from(2_u8),
                worker_limit: BigUint::from(configured_workers),
                workers_used: BigUint::from(2_u8),
                batches: BigUint::from(2_u8),
                joins: BigUint::from(1_u8),
            },
        ))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CpuExecutionReceipt {
    pub schema: String,
    pub mode: String,
    pub tasks: BigUint,
    pub worker_limit: BigUint,
    pub workers_used: BigUint,
    pub batches: BigUint,
    pub joins: BigUint,
}

impl CpuExecutionReceipt {
    /// Compose physical testimony for CPU components which used the same apparatus in sequence.
    ///
    /// Unlike [`Self::ordered_antichains`], this says nothing about causal dependence between the
    /// components. It records only that their physical worker apertures did not overlap in wall
    /// time, so the greatest component width is the greatest simultaneous worker population.
    pub fn sequential_components(receipts: &[Self]) -> Self {
        let mode = receipts
            .first()
            .map_or_else(|| "serial".to_owned(), |receipt| receipt.mode.clone());
        let mut aggregate = Self {
            schema: "holonic-engine.cpu-execution-receipt.v1".to_owned(),
            mode,
            tasks: BigUint::from(0_u8),
            worker_limit: BigUint::from(0_u8),
            workers_used: BigUint::from(0_u8),
            batches: BigUint::from(0_u8),
            joins: BigUint::from(0_u8),
        };
        for receipt in receipts {
            aggregate.tasks += &receipt.tasks;
            aggregate.worker_limit = aggregate.worker_limit.max(receipt.worker_limit.clone());
            aggregate.workers_used = aggregate.workers_used.max(receipt.workers_used.clone());
            aggregate.batches += &receipt.batches;
            aggregate.joins += &receipt.joins;
        }
        aggregate
    }

    /// Compose the physical testimony of causally ordered antichains.
    ///
    /// Tasks inside one receipt may have run together. Receipts in this slice
    /// are ordered because each antichain consumes the exact successor of the
    /// preceding antichain. Summing work while retaining the greatest
    /// simultaneous worker population records both facts without turning
    /// scheduling into causality.
    pub fn ordered_antichains(receipts: &[Self]) -> Self {
        Self::sequential_components(receipts)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CpuExecutionError<E> {
    #[error("one exact CPU work member refused")]
    Operation(E),
    #[error("one physical CPU worker panicked before returning its local batch")]
    WorkerPanicked,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::sync::Mutex;

    #[test]
    fn multicore_completion_cannot_reorder_the_logical_result() {
        let inputs = (0_u64..31).collect::<Vec<_>>();
        let serial = CpuExecutor::serial()
            .execute_indexed(&inputs, |_index, value| Ok::<_, ()>(value * value))
            .unwrap()
            .0;
        let parallel = CpuExecutor::multicore(NonZeroUsize::new(4).unwrap())
            .execute_indexed(&inputs, |_index, value| Ok::<_, ()>(value * value))
            .unwrap()
            .0;
        assert_eq!(serial, parallel);
    }

    #[test]
    fn heterogeneous_independent_pair_retains_declared_return_address() {
        let executor = CpuExecutor::multicore(NonZeroUsize::new(4).unwrap());
        let (left, right, receipt) = executor
            .execute_independent_pair(|| "left", || 41_u64 + 1)
            .unwrap();
        assert_eq!(left, "left");
        assert_eq!(right, 42);
        assert_eq!(receipt.workers_used, BigUint::from(2_u8));
    }

    #[test]
    fn worker_receipt_names_the_threads_actually_spawned() {
        let inputs = (0_u64..14).collect::<Vec<_>>();
        let observed = Mutex::new(HashSet::new());
        let (_, receipt) = CpuExecutor::multicore(NonZeroUsize::new(12).unwrap())
            .execute_indexed(&inputs, |_index, value| {
                observed
                    .lock()
                    .expect("worker observation lock remains live")
                    .insert(std::thread::current().id());
                Ok::<_, ()>(*value)
            })
            .unwrap();
        assert_eq!(observed.into_inner().unwrap().len(), 12);
        assert_eq!(receipt.workers_used, BigUint::from(12_u8));
        assert_eq!(receipt.batches, BigUint::from(12_u8));
        assert_eq!(receipt.joins, BigUint::from(12_u8));
    }
}
