//! **Ports `Π`: flow–effort bonds and their power.**
//!
//! [definition] A bond is a flow and an effort on one interface index set
//! (`Holon/Port.lean::Bond`, `Holon/Port.lean::flow`, `Holon/Port.lean::effort`); its power is
//! `⟨e, f⟩` (`Holon/Port.lean::power`) and the symmetric bond pairing
//! `⟨⟨(f₁,e₁),(f₂,e₂)⟩⟩ = ⟨e₁,f₂⟩ + ⟨e₂,f₁⟩` is `Holon/Port.lean::bondForm`, symmetric
//! (`Holon/Port.lean::bondForm_symm`), with `⟨⟨b,b⟩⟩ = 2·power b`
//! (`Holon/Port.lean::bondForm_self`) and nondegenerate
//! (`Holon/Port.lean::bondForm_nondegenerate`).
//!
//! [definition; agent-inferred] **Units.** The engine's `quantity::{Dimension, Quantity}` cannot be
//! reused here: `holonic-engine` depends on this crate, and `relational-geometry` carries no
//! dimension type. [`Dimension`] is therefore a minimal typed exponent vector over named base
//! dimensions, and [`PortUnits`] checks `power = flow · effort` at construction. Its adapter to
//! `JointUnits`/`Quantity` belongs with the engine consumer (plan phase 3 integration).
//!
//! | Lean | Rust |
//! |---|---|
//! | `Bond`, `flow`, `effort` | [`Bond`] |
//! | `power` | [`Bond::power`] |
//! | `bondForm`, `bondForm_symm`, `bondForm_self` | [`Bond::pairing`] |
//! | `bondForm_separating` | [`Bond::pairing`] against unit bonds (tests) |

use std::collections::BTreeMap;

use crate::geometry::Rat;
use serde::{Deserialize, Serialize};

use crate::holon::HolonError;
use crate::scalar::{add, dot, neg};

/// [definition] A bond: one flow and one effort per port (`Holon/Port.lean::Bond`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Bond {
    flow: Vec<Rat>,
    effort: Vec<Rat>,
}

impl Bond {
    /// A bond on `flow.len()` ports; the effort must carry one entry per port.
    pub fn new(flow: Vec<Rat>, effort: Vec<Rat>) -> Result<Self, HolonError> {
        if flow.len() != effort.len() {
            return Err(HolonError::Shape {
                what: "bond effort",
                expected: flow.len(),
                found: effort.len(),
            });
        }
        Ok(Self { flow, effort })
    }

    /// The zero bond on `ports` ports.
    pub fn zero(ports: usize) -> Self {
        Self {
            flow: crate::scalar::zeros(ports),
            effort: crate::scalar::zeros(ports),
        }
    }

    pub fn ports(&self) -> usize {
        self.flow.len()
    }

    pub fn flow(&self) -> &[Rat] {
        &self.flow
    }

    pub fn effort(&self) -> &[Rat] {
        &self.effort
    }

    /// The bond as one coordinate vector `[f; e]` of length `2n`.
    pub fn coordinates(&self) -> Vec<Rat> {
        let mut out = self.flow.clone();
        out.extend(self.effort.iter().cloned());
        out
    }

    /// Read a `[f; e]` coordinate vector of even length.
    pub fn from_coordinates(coordinates: &[Rat]) -> Result<Self, HolonError> {
        if !coordinates.len().is_multiple_of(2) {
            return Err(HolonError::Shape {
                what: "bond coordinates (even length)",
                expected: coordinates.len() + 1,
                found: coordinates.len(),
            });
        }
        let n = coordinates.len() / 2;
        Ok(Self {
            flow: coordinates[..n].to_vec(),
            effort: coordinates[n..].to_vec(),
        })
    }

    /// [definition] The power `⟨e, f⟩` (`Holon/Port.lean::power`).
    pub fn power(&self) -> Rat {
        dot(&self.effort, &self.flow)
    }

    /// [definition] The bond pairing `⟨e₁,f₂⟩ + ⟨e₂,f₁⟩` (`Holon/Port.lean::bondForm`).
    pub fn pairing(&self, other: &Self) -> Result<Rat, HolonError> {
        if self.ports() != other.ports() {
            return Err(HolonError::Shape {
                what: "paired bond",
                expected: self.ports(),
                found: other.ports(),
            });
        }
        Ok(dot(&self.effort, &other.flow) + dot(&other.effort, &self.flow))
    }

    pub fn sum(&self, other: &Self) -> Result<Self, HolonError> {
        if self.ports() != other.ports() {
            return Err(HolonError::Shape {
                what: "summed bond",
                expected: self.ports(),
                found: other.ports(),
            });
        }
        Ok(Self {
            flow: add(&self.flow, &other.flow),
            effort: add(&self.effort, &other.effort),
        })
    }

    /// `(−f, e)`: the same bond seen from the other side of a shared port
    /// (`Holon/Dirac.lean::link`).
    pub fn reversed_flow(&self) -> Self {
        Self {
            flow: neg(&self.flow),
            effort: self.effort.clone(),
        }
    }

    /// The bond restricted to the listed ports, in the listed order.
    pub fn select(&self, ports: &[usize]) -> Result<Self, HolonError> {
        if let Some(bad) = ports.iter().find(|port| **port >= self.ports()) {
            return Err(HolonError::PortOutside {
                port: *bad,
                ports: self.ports(),
            });
        }
        Ok(Self {
            flow: ports.iter().map(|port| self.flow[*port].clone()).collect(),
            effort: ports
                .iter()
                .map(|port| self.effort[*port].clone())
                .collect(),
        })
    }

    /// Concatenate the ports of two bonds.
    pub fn concat(&self, other: &Self) -> Self {
        let mut flow = self.flow.clone();
        flow.extend(other.flow.iter().cloned());
        let mut effort = self.effort.clone();
        effort.extend(other.effort.iter().cloned());
        Self { flow, effort }
    }
}

/// [definition; agent-inferred] A physical dimension as integer exponents over named base
/// dimensions. The empty map is dimensionless.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct Dimension {
    exponents: BTreeMap<String, i64>,
}

impl Dimension {
    pub fn dimensionless() -> Self {
        Self::default()
    }

    /// One base dimension to the first power.
    pub fn base(name: &str) -> Self {
        Self::default().times(&Self::power_of(name, 1))
    }

    /// One base dimension to an integer power.
    pub fn power_of(name: &str, exponent: i64) -> Self {
        let mut exponents = BTreeMap::new();
        if exponent != 0 {
            exponents.insert(name.to_owned(), exponent);
        }
        Self { exponents }
    }

    pub fn exponent(&self, name: &str) -> i64 {
        self.exponents.get(name).copied().unwrap_or(0)
    }

    pub fn is_dimensionless(&self) -> bool {
        self.exponents.is_empty()
    }

    /// The product dimension; exponents add and zero exponents are dropped, so equality is
    /// structural.
    pub fn times(&self, other: &Self) -> Self {
        let mut exponents = self.exponents.clone();
        for (name, exponent) in &other.exponents {
            let entry = exponents.entry(name.clone()).or_insert(0);
            *entry += exponent;
            if *entry == 0 {
                exponents.remove(name);
            }
        }
        Self { exponents }
    }

    pub fn inverse(&self) -> Self {
        Self {
            exponents: self
                .exponents
                .iter()
                .map(|(name, exponent)| (name.clone(), -exponent))
                .collect(),
        }
    }
}

/// [definition] The units of one port: flow, effort and their product, the power.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortUnits {
    flow: Dimension,
    effort: Dimension,
    power: Dimension,
}

impl PortUnits {
    /// Declared flow and effort; the power dimension is their product.
    pub fn new(flow: Dimension, effort: Dimension) -> Self {
        let power = flow.times(&effort);
        Self {
            flow,
            effort,
            power,
        }
    }

    /// Declared flow, effort and power; refuses when `power ≠ flow · effort`.
    pub fn declared(
        flow: Dimension,
        effort: Dimension,
        power: Dimension,
    ) -> Result<Self, HolonError> {
        if flow.times(&effort) != power {
            return Err(HolonError::UnitsMismatch);
        }
        Ok(Self {
            flow,
            effort,
            power,
        })
    }

    /// A port whose effort is `power / flow`: the effort is derived, never guessed.
    pub fn from_flow_and_power(flow: Dimension, power: Dimension) -> Self {
        let effort = power.times(&flow.inverse());
        Self {
            flow,
            effort,
            power,
        }
    }

    pub fn flow(&self) -> &Dimension {
        &self.flow
    }

    pub fn effort(&self) -> &Dimension {
        &self.effort
    }

    pub fn power(&self) -> &Dimension {
        &self.power
    }
}

/// [definition] The four port kinds of a port Holon, in the order the ports are laid out:
/// storage `σ`, resistive `ρ`, external `π`, active `α` (`Holon/Element.lean::Ports`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PortKind {
    Storage,
    Resistive,
    External,
    Active,
}

/// [definition] A named port with its kind and units.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Port {
    pub name: String,
    pub kind: PortKind,
    pub units: PortUnits,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{int, ints};

    #[test]
    fn the_pairing_is_symmetric_and_reads_twice_the_power() {
        let b = Bond::new(ints(&[1, 2]), ints(&[3, -1])).unwrap();
        let c = Bond::new(ints(&[0, 5]), ints(&[2, 7])).unwrap();
        assert_eq!(b.pairing(&c).unwrap(), c.pairing(&b).unwrap());
        assert_eq!(b.pairing(&b).unwrap(), int(2) * b.power());
        assert_eq!(b.power(), int(1));
    }

    /// `Holon/Port.lean::bondForm_separating`: a bond pairing to zero against every unit bond is
    /// zero; a nonzero bond is seen by one of them.
    #[test]
    fn a_nonzero_bond_is_seen_by_a_unit_bond() {
        let b = Bond::new(ints(&[0, 4]), ints(&[0, 0])).unwrap();
        let unit_effort = Bond::new(ints(&[0, 0]), ints(&[0, 1])).unwrap();
        assert_eq!(b.pairing(&unit_effort).unwrap(), int(4));
    }

    #[test]
    fn units_refuse_a_power_that_is_not_flow_times_effort() {
        let current = Dimension::base("A");
        let volt = Dimension::base("W").times(&current.inverse());
        let units = PortUnits::new(current.clone(), volt.clone());
        assert_eq!(units.power(), &Dimension::base("W"));
        assert!(PortUnits::declared(current.clone(), volt, Dimension::base("W")).is_ok());
        assert_eq!(
            PortUnits::declared(current.clone(), current, Dimension::base("W")),
            Err(HolonError::UnitsMismatch)
        );
    }
}
