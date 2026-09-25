//! Schnakenberg's production across a neck, carried as exact ratios.

use std::collections::BTreeSet;

use num_traits::Zero;

use crate::aeon::MarkovChain;
use crate::ratio::Rat;
use crate::ratio::surprisal::SymbolicSurprisal;

use super::{ThermalError, positive};

/// [definition] **One junction of a neck**: its forward and backward flows `J₊, J₋ > 0` on one
/// clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JunctionFlow {
    forward: Rat,
    backward: Rat,
}

impl JunctionFlow {
    pub fn new(forward: Rat, backward: Rat) -> Result<Self, ThermalError> {
        positive("a forward flow", &forward)?;
        positive("a backward flow", &backward)?;
        Ok(Self { forward, backward })
    }

    pub fn forward(&self) -> &Rat {
        &self.forward
    }

    pub fn backward(&self) -> &Rat {
        &self.backward
    }

    /// The net current `J₊ − J₋`.
    pub fn net(&self) -> Rat {
        &self.forward - &self.backward
    }

    /// The flow ratio `J₊/J₋`, the operand of the logarithm.
    pub fn ratio(&self) -> Rat {
        &self.forward / &self.backward
    }

    /// [proved-derived; implemented-exact] **The rational sign certificate**
    /// `(J₊ − J₋)(J₊/J₋ − 1) = (J₊ − J₋)²/J₋ ≥ 0`, zero exactly when balanced (Lean
    /// `Physics/Thermal/Schnakenberg.certificate_eq`, `certificate_eq_zero_iff`).
    pub fn certificate(&self) -> Rat {
        let net = self.net();
        &net * &net / &self.backward
    }

    pub fn is_balanced(&self) -> bool {
        self.forward == self.backward
    }

    /// `(J₊ − J₋) log₂(J₊/J₋)`, in bits.
    fn production(&self) -> Result<SymbolicSurprisal, ThermalError> {
        Ok(SymbolicSurprisal::log2_of_ratio(&self.ratio())?.scaled(&self.net()))
    }
}

/// [definition] **Schnakenberg's production across a neck**: `σ = Σ (J₊ − J₋) log₂(J₊/J₋)` in
/// bits, the exact form of the pairs `(J₊ − J₋, J₊/J₋)` (Lean
/// `Physics/Thermal/Schnakenberg.neckProduction_eq_edgeCode`; natural units are `ln 2` times it).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeckProduction {
    junctions: Vec<JunctionFlow>,
    production: SymbolicSurprisal,
}

impl NeckProduction {
    /// The production across the junctions of a neck.
    pub fn across(junctions: Vec<JunctionFlow>) -> Result<Self, ThermalError> {
        let mut production = SymbolicSurprisal::zero();
        for junction in &junctions {
            production = production.plus(&junction.production()?);
        }
        Ok(Self {
            junctions,
            production,
        })
    }

    pub fn junctions(&self) -> &[JunctionFlow] {
        &self.junctions
    }

    /// `σ` in bits, as its exact form. A numeric value is its enclosure, an exterior face.
    pub fn production(&self) -> &SymbolicSurprisal {
        &self.production
    }

    /// [proved-derived; implemented-exact] **The neck's certificate** `Σ (J₊ − J₋)²/J₋ ≥ 0`,
    /// positive exactly when the production is (Lean `term_pos_iff_certificate_pos`).
    pub fn certificate(&self) -> Rat {
        self.junctions.iter().map(JunctionFlow::certificate).sum()
    }

    /// [proved-derived; implemented-exact] **Balanced exactly when `σ = 0`** (Lean
    /// `neckProduction_eq_zero_iff`), decided on the rationals.
    pub fn is_balanced(&self) -> bool {
        self.junctions.iter().all(JunctionFlow::is_balanced)
    }
}

/// [proved-derived; implemented-exact] **The production across the cut of a chain's section**:
/// the junctions `x → y` with `x` in the section and `y` outside it, at flows
/// `J(x,y) = π(x) P(x,y)`. It is at most the chain's epoch production, with equality exactly when
/// every junction inside either side is balanced (Lean
/// `Physics/Thermal/Schnakenberg.epochProduction_eq_cut_add_interior`,
/// `cutProduction_eq_epochProduction_iff`). The section is a set of states: a repeated state and a
/// state outside the chain are refused, as is a junction that carries flow one way only.
pub fn cut_production(
    chain: &MarkovChain,
    law: &[Rat],
    section: &[usize],
) -> Result<NeckProduction, ThermalError> {
    let states = chain.states();
    if law.len() != states {
        return Err(ThermalError::Shape {
            what: "law (one mass per state)",
            expected: states,
            found: law.len(),
        });
    }
    let mut inside = BTreeSet::new();
    for &cell in section {
        if cell >= states {
            return Err(ThermalError::Shape {
                what: "section state below the chain's state count",
                expected: states,
                found: cell,
            });
        }
        if !inside.insert(cell) {
            return Err(ThermalError::RepeatedCell { cell });
        }
    }
    let mut junctions = Vec::new();
    for &x in &inside {
        for y in (0..states).filter(|y| !inside.contains(y)) {
            let forward = &law[x] * chain.probability(x, y);
            let backward = &law[y] * chain.probability(y, x);
            match (forward.is_zero(), backward.is_zero()) {
                (true, true) => {}
                (false, true) => return Err(ThermalError::IrreversibleJunction { from: x, to: y }),
                (true, false) => return Err(ThermalError::IrreversibleJunction { from: y, to: x }),
                (false, false) => junctions.push(JunctionFlow::new(forward, backward)?),
            }
        }
    }
    NeckProduction::across(junctions)
}
