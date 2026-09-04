//! Exact host/device execution boundary.
//!
//! A GPU API may realize this ABI, but it is not mathematical authority.
//! Admission requires byte-for-byte equality of the exact returned carrier
//! against the CPU realization on a declared corpus.  Fixed-function graphics
//! state, shader floating point, and hidden tessellation have no entry here.

use num_bigint::BigUint;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{HomogeneousConic, ProjectiveTurn};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DeviceBackend {
    HostCpu,
    VulkanCompute,
    CudaCompute,
    OtherExact,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactDeviceTask {
    ProjectiveTurn {
        turn: ProjectiveTurn,
        input: Rat,
    },
    EvaluateConic {
        form: Box<HomogeneousConic>,
        point: [Rat; 3],
    },
    AccumulateCurrent {
        oriented_terms: Vec<Rat>,
        declared_source: Rat,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactDeviceResult {
    ProjectiveValue(Option<Rat>),
    ConicValue(Rat),
    CurrentResidual(Rat),
}

pub trait ExactDeviceExecutor {
    fn backend(&self) -> DeviceBackend;

    fn execute(
        &self,
        tasks: &[ExactDeviceTask],
    ) -> Result<Vec<ExactDeviceResult>, ExactDeviceError>;
}

#[derive(Clone, Copy, Debug, Default)]
pub struct HostExactDevice;

impl ExactDeviceExecutor for HostExactDevice {
    fn backend(&self) -> DeviceBackend {
        DeviceBackend::HostCpu
    }

    fn execute(
        &self,
        tasks: &[ExactDeviceTask],
    ) -> Result<Vec<ExactDeviceResult>, ExactDeviceError> {
        Ok(tasks
            .iter()
            .map(|task| match task {
                ExactDeviceTask::ProjectiveTurn { turn, input } => {
                    ExactDeviceResult::ProjectiveValue(turn.apply(input))
                }
                ExactDeviceTask::EvaluateConic { form, point } => {
                    ExactDeviceResult::ConicValue(form.evaluate(point))
                }
                ExactDeviceTask::AccumulateCurrent {
                    oriented_terms,
                    declared_source,
                } => ExactDeviceResult::CurrentResidual(
                    oriented_terms
                        .iter()
                        .fold(Rat::from_integer(0.into()), |sum, term| sum + term)
                        - declared_source,
                ),
            })
            .collect())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceParityReceipt {
    pub schema: String,
    pub candidate: DeviceBackend,
    pub tasks: BigUint,
    pub exact: bool,
}

/// Admit a physical backend only when it preserves the complete exact ABI.
pub fn admit_device(
    candidate: &impl ExactDeviceExecutor,
    tasks: &[ExactDeviceTask],
) -> Result<DeviceParityReceipt, ExactDeviceError> {
    let authority = HostExactDevice.execute(tasks)?;
    let returned = candidate.execute(tasks)?;
    if returned.len() != authority.len() {
        return Err(ExactDeviceError::Cardinality {
            expected: authority.len(),
            actual: returned.len(),
        });
    }
    if returned != authority {
        return Err(ExactDeviceError::ParityRefused(candidate.backend()));
    }
    Ok(DeviceParityReceipt {
        schema: "holonic-engine.device-parity.v1".to_owned(),
        candidate: candidate.backend(),
        tasks: BigUint::from(tasks.len()),
        exact: true,
    })
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactDeviceError {
    #[error("device returned {actual} members for {expected} exact tasks")]
    Cardinality { expected: usize, actual: usize },
    #[error("{0:?} failed exact host/device parity and cannot execute the live law")]
    ParityRefused(DeviceBackend),
    #[error("the physical device executor refused: {0}")]
    PhysicalRefusal(String),
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;

    #[test]
    fn host_exact_abi_closes_its_own_admission_corpus() {
        let tasks = vec![
            ExactDeviceTask::ProjectiveTurn {
                turn: ProjectiveTurn::identity(),
                input: integer(7),
            },
            ExactDeviceTask::EvaluateConic {
                form: Box::new(
                    HomogeneousConic::new([
                        integer(1),
                        integer(0),
                        integer(1),
                        integer(0),
                        integer(0),
                        integer(-1),
                    ])
                    .unwrap(),
                ),
                point: [integer(1), integer(0), integer(1)],
            },
            ExactDeviceTask::AccumulateCurrent {
                oriented_terms: vec![integer(3), integer(-2)],
                declared_source: integer(1),
            },
        ];
        assert!(admit_device(&HostExactDevice, &tasks).unwrap().exact);
    }
}
