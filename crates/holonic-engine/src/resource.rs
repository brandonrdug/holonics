//! Receiver-declared resource faces of an algorithm.
//!
//! Big-O, elapsed time, bytes moved, and energy are different receivers.  No
//! one scalar is allowed to impersonate the complete physical execution.

use std::collections::BTreeMap;

use num_bigint::BigUint;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::{CausalDiagram, DiagramError};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MemoryTier {
    Register,
    LocalScratch,
    Cache(u8),
    MainMemory,
    DeviceMemory,
    CpuDeviceLink,
    DurableStorage,
    Network,
    Declared(String),
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Traffic {
    pub read_octets: BigUint,
    pub written_octets: BigUint,
    pub messages: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LogicalResourceReceipt {
    pub schema: String,
    pub work: BigUint,
    pub causal_span: BigUint,
    /// Largest layer exposed by one deterministic topological layering.
    /// It is a usable co-present frontier, not a claim that the hardware ran
    /// every member simultaneously.
    pub exposed_parallel_width: BigUint,
    pub events_by_law: BTreeMap<String, BigUint>,
}

impl LogicalResourceReceipt {
    pub fn from_diagram(diagram: &CausalDiagram) -> Result<Self, DiagramError> {
        let layers = diagram.layers()?;
        let mut events_by_law = BTreeMap::<String, BigUint>::new();
        for event in diagram.events.values() {
            *events_by_law.entry(event.law.clone()).or_default() += BigUint::one();
        }
        let exposed_parallel_width = layers
            .iter()
            .map(|layer| BigUint::from(layer.len()))
            .max()
            .unwrap_or_else(BigUint::zero);
        Ok(Self {
            schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
            work: BigUint::from(diagram.events.len()),
            causal_span: BigUint::from(layers.len()),
            exposed_parallel_width,
            events_by_law,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhysicalResourceReceipt {
    pub schema: String,
    pub executor: String,
    /// Exact physical counts supplied by the executor or a declared hardware
    /// model. Missing tiers remain unknown rather than silently becoming zero.
    pub traffic: BTreeMap<MemoryTier, Traffic>,
    /// Peak simultaneously resident octets observed at each physical tier.
    pub resident_peak_octets: BTreeMap<MemoryTier, BigUint>,
    pub synchronization_events: BigUint,
    pub clock_cycles: Option<BigUint>,
    pub irreversible_merges: Option<BigUint>,
}

impl PhysicalResourceReceipt {
    pub fn new(executor: impl Into<String>) -> Self {
        Self {
            schema: "holonic-engine.physical-resource-receipt.v1".to_owned(),
            executor: executor.into(),
            traffic: BTreeMap::new(),
            resident_peak_octets: BTreeMap::new(),
            synchronization_events: BigUint::zero(),
            clock_cycles: None,
            irreversible_merges: None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnergyCoefficients {
    /// Energy per read octet at each declared tier.
    pub read: BTreeMap<MemoryTier, Rat>,
    /// Energy per written octet at each declared tier.
    pub write: BTreeMap<MemoryTier, Rat>,
    /// Energy per message or synchronization aperture.
    pub message: BTreeMap<MemoryTier, Rat>,
    pub synchronization: Option<Rat>,
    /// A declared coefficient per logically irreversible merge. This may be a
    /// measured device coefficient or a thermodynamic model; the receipt does
    /// not confuse the two.
    pub irreversible_merge: Option<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EnergyReceipt {
    pub schema: String,
    pub exact_energy: Rat,
    pub model_name: String,
}

/// Evaluate energy only when every physically observed term has a declared
/// coefficient.  Incompleteness returns `None`; it never fabricates zero cost.
pub fn evaluate_energy(
    physical: &PhysicalResourceReceipt,
    coefficients: &EnergyCoefficients,
    model_name: impl Into<String>,
) -> Option<EnergyReceipt> {
    let mut total = Rat::zero();
    for (tier, traffic) in &physical.traffic {
        if !traffic.read_octets.is_zero() {
            total += coefficients.read.get(tier)?
                * Rat::from_integer(traffic.read_octets.clone().into());
        }
        if !traffic.written_octets.is_zero() {
            total += coefficients.write.get(tier)?
                * Rat::from_integer(traffic.written_octets.clone().into());
        }
        if !traffic.messages.is_zero() {
            total += coefficients.message.get(tier)?
                * Rat::from_integer(traffic.messages.clone().into());
        }
    }
    if !physical.synchronization_events.is_zero() {
        total += coefficients.synchronization.as_ref()?
            * Rat::from_integer(physical.synchronization_events.clone().into());
    }
    if let Some(merges) = &physical.irreversible_merges
        && !merges.is_zero()
    {
        total +=
            coefficients.irreversible_merge.as_ref()? * Rat::from_integer(merges.clone().into());
    }
    Some(EnergyReceipt {
        schema: "holonic-engine.energy-receipt.v1".to_owned(),
        exact_energy: total,
        model_name: model_name.into(),
    })
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;

    #[test]
    fn energy_refuses_an_unpriced_physical_current() {
        let mut receipt = PhysicalResourceReceipt::new("declared CPU");
        receipt.traffic.insert(
            MemoryTier::MainMemory,
            Traffic {
                read_octets: BigUint::from(8_u8),
                ..Traffic::default()
            },
        );
        assert_eq!(
            evaluate_energy(&receipt, &EnergyCoefficients::default(), "incomplete"),
            None
        );
    }

    #[test]
    fn energy_remains_an_exact_ratio() {
        let mut receipt = PhysicalResourceReceipt::new("declared CPU");
        receipt.traffic.insert(
            MemoryTier::MainMemory,
            Traffic {
                read_octets: BigUint::from(3_u8),
                written_octets: BigUint::from(2_u8),
                messages: BigUint::zero(),
            },
        );
        let mut coefficients = EnergyCoefficients::default();
        coefficients.read.insert(
            MemoryTier::MainMemory,
            Rat::new(BigInt::from(1), BigInt::from(3)),
        );
        coefficients.write.insert(
            MemoryTier::MainMemory,
            Rat::new(BigInt::from(1), BigInt::from(2)),
        );
        let energy = evaluate_energy(&receipt, &coefficients, "exact declared model").unwrap();
        assert_eq!(energy.exact_energy, Rat::from_integer(BigInt::from(2)));
    }
}
