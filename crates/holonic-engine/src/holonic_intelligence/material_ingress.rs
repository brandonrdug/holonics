//! Finest-occurrence octet current before any native route is selected.
//!
//! Octets are exterior material faces. Their ordered boundary differences become exact current;
//! the caller-declared ingress address remains separate and no byte, filename, language, format,
//! hash, or expected answer selects a native state.

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::ExactComplexWaveCurrent;

pub const NATIVE_MATERIAL_CURRENT_SCHEMA: &str = "holonic-engine.native-material-current.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialCurrentOccurrence {
    pub ordinal: u64,
    pub boundary_difference: i16,
    pub current: ExactComplexWaveCurrent,
}

/// Complete ordered current at the finest occurrence grain supplied by the exterior port.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialCurrent {
    pub schema: String,
    pub occurrences: Vec<NativeMaterialCurrentOccurrence>,
    pub integrated_current: ExactComplexWaveCurrent,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeMaterialCurrentError {
    #[error("the exterior material occurrence is empty")]
    Empty,
    #[error("the exterior material current is malformed")]
    Malformed,
}

impl NativeMaterialCurrent {
    pub fn from_octets(octets: &[u8]) -> Result<Self, NativeMaterialCurrentError> {
        if octets.is_empty() {
            return Err(NativeMaterialCurrentError::Empty);
        }
        let mut previous = 0_i16;
        let mut integrated = ExactComplexWaveCurrent::zero();
        let mut occurrences = Vec::with_capacity(octets.len());
        for (ordinal, octet) in octets.iter().copied().enumerate() {
            let current_value = i16::from(octet);
            let boundary_difference = current_value - previous;
            let current = exact_current(boundary_difference);
            integrated = integrated.add(&current);
            occurrences.push(NativeMaterialCurrentOccurrence {
                ordinal: u64::try_from(ordinal)
                    .map_err(|_| NativeMaterialCurrentError::Malformed)?,
                boundary_difference,
                current,
            });
            previous = current_value;
        }
        let material = Self {
            schema: NATIVE_MATERIAL_CURRENT_SCHEMA.to_owned(),
            occurrences,
            integrated_current: integrated,
        };
        material.validate()?;
        Ok(material)
    }

    pub fn validate(&self) -> Result<(), NativeMaterialCurrentError> {
        if self.schema != NATIVE_MATERIAL_CURRENT_SCHEMA || self.occurrences.is_empty() {
            return Err(NativeMaterialCurrentError::Malformed);
        }
        let mut integrated = ExactComplexWaveCurrent::zero();
        for (ordinal, occurrence) in self.occurrences.iter().enumerate() {
            if occurrence.ordinal != ordinal as u64
                || occurrence.current != exact_current(occurrence.boundary_difference)
            {
                return Err(NativeMaterialCurrentError::Malformed);
            }
            integrated = integrated.add(&occurrence.current);
        }
        if integrated != self.integrated_current {
            return Err(NativeMaterialCurrentError::Malformed);
        }
        Ok(())
    }
}

fn exact_current(value: i16) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(value)),
        Rat::from_integer(BigInt::from(0)),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_octet_differences_return_complete_exact_current() {
        let current = NativeMaterialCurrent::from_octets(&[3, 8, 2]).expect("current");
        assert_eq!(
            current
                .occurrences
                .iter()
                .map(|occurrence| occurrence.boundary_difference)
                .collect::<Vec<_>>(),
            vec![3, 5, -6]
        );
        assert_eq!(current.integrated_current, exact_current(2));
        assert!(current.validate().is_ok());
    }

    #[test]
    fn changing_one_octet_changes_the_ordered_current_before_its_scalar_sum() {
        let left = NativeMaterialCurrent::from_octets(&[3, 8, 2]).expect("left");
        let right = NativeMaterialCurrent::from_octets(&[4, 8, 2]).expect("right");
        assert_eq!(left.integrated_current, right.integrated_current);
        assert_ne!(left.occurrences, right.occurrences);
        assert_eq!(
            NativeMaterialCurrent::from_octets(&[]),
            Err(NativeMaterialCurrentError::Empty)
        );
    }
}
