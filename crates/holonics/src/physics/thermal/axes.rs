//! The time and entropy axes along an oriented chain (#5).

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use crate::aeon::{Aeon, MarkovChain, Transition, epochs};
use crate::ratio::Rat;
use crate::ratio::surprisal::SymbolicSurprisal;

use super::ThermalError;
use super::neck::{JunctionFlow, NeckProduction};

/// [definition] **An oriented chain of cells**: a nearest-neighbour Markov chain whose junction
/// `i` runs from cell `i` to cell `i + 1`, either **open** (a path, with a declared carry section)
/// or closed into a **ring** through its carry section `N − 1 → 0` (Lean
/// `Physics/Thermal/ChainAxes.NearestNeighbour`, the ring of `ringProduction`). The **carry
/// junction** is the section at which the longitudinal axis counts epochs and the entropy
/// coordinate takes its carry; it is not a neck (a bottleneck of least forward flow), which
/// bounds the current at every junction alike.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OrientedChain {
    chain: MarkovChain,
    closed: bool,
    carry: usize,
}

/// [definition] **The two-axis reading of an aeon**: the signed epochs at the carry section (the
/// longitudinal axis), the heat (the entropy axis, as the ratio product of the step affinities),
/// the state ratio `R(end)/R(start)` of the entropy coordinate and the ring's turn.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoAxisReading {
    /// Forward minus backward crossings of the carry section (Lean `signed_count_is_flux`).
    pub longitudinal: BigInt,
    /// `Π P(x→y)/P(y→x)` over the aeon's steps ([`MarkovChain::heat`]); its log is the entropy
    /// reading.
    pub entropy: Rat,
    /// `R(end)/R(start)`, the entropy coordinate's change as a ratio.
    pub state: Rat,
    /// The cycle ratio product; one on an open chain.
    pub turn: Rat,
}

impl TwoAxisReading {
    /// `turnⁿ`, `n` the signed epochs at the carry section.
    pub fn winding_term(&self) -> Rat {
        let mut base = if self.longitudinal.is_negative() {
            self.turn.recip()
        } else {
            self.turn.clone()
        };
        let mut exponent = self.longitudinal.magnitude().clone();
        let mut result = Rat::one();
        while !exponent.is_zero() {
            if exponent.bit(0) {
                result *= &base;
            }
            base = &base * &base;
            exponent >>= 1;
        }
        result
    }

    /// [proved-derived; implemented-exact] **The axes cross at the carry section**:
    /// `entropy = state · turnⁿ` (Lean `Physics/Thermal/ChainAxes.entropy_reading`, in the
    /// multiplicative chart).
    pub fn crosses(&self) -> bool {
        self.entropy == &self.state * self.winding_term()
    }
}

impl OrientedChain {
    /// **An open chain** with its carry section at `carry` (`carry → carry + 1`). Refused when a
    /// transition skips a cell.
    pub fn open(chain: MarkovChain, carry: usize) -> Result<Self, ThermalError> {
        let cells = chain.states();
        if cells < 2 {
            return Err(ThermalError::TooFewCells {
                what: "an open chain",
                least: 2,
                found: cells,
            });
        }
        if carry + 1 >= cells {
            return Err(ThermalError::Shape {
                what: "carry section below the last cell",
                expected: cells - 1,
                found: carry,
            });
        }
        for from in 0..cells {
            for to in 0..cells {
                if chain.probability(from, to).is_positive() && from.abs_diff(to) > 1 {
                    return Err(ThermalError::NotNearestNeighbour { from, to });
                }
            }
        }
        Ok(Self {
            chain,
            closed: false,
            carry,
        })
    }

    /// **A ring** of at least three cells, closed through its carry section `N − 1 → 0`. Refused
    /// when a transition skips a cell of the ring.
    pub fn ring(chain: MarkovChain) -> Result<Self, ThermalError> {
        let cells = chain.states();
        if cells < 3 {
            return Err(ThermalError::TooFewCells {
                what: "a ring",
                least: 3,
                found: cells,
            });
        }
        for from in 0..cells {
            for to in 0..cells {
                let neighbour = to == from || to == (from + 1) % cells || from == (to + 1) % cells;
                if chain.probability(from, to).is_positive() && !neighbour {
                    return Err(ThermalError::NotNearestNeighbour { from, to });
                }
            }
        }
        Ok(Self {
            chain,
            closed: true,
            carry: cells - 1,
        })
    }

    pub fn chain(&self) -> &MarkovChain {
        &self.chain
    }

    pub fn cells(&self) -> usize {
        self.chain.states()
    }

    pub fn is_ring(&self) -> bool {
        self.closed
    }

    /// The carry section, oriented.
    pub fn carry_section(&self) -> Transition {
        Transition {
            from: self.carry,
            to: (self.carry + 1) % self.cells(),
        }
    }

    fn junctions(&self) -> usize {
        if self.closed {
            self.cells()
        } else {
            self.cells() - 1
        }
    }

    /// The affinity ratio of junction `i`, `P(i → i+1)/P(i+1 → i)`.
    fn affinity(&self, junction: usize) -> Result<Rat, ThermalError> {
        let (from, to) = (junction, (junction + 1) % self.cells());
        let forward = self.chain.probability(from, to);
        let backward = self.chain.probability(to, from);
        if !forward.is_positive() {
            return Err(ThermalError::IrreversibleJunction { from: to, to: from });
        }
        if !backward.is_positive() {
            return Err(ThermalError::IrreversibleJunction { from, to });
        }
        Ok(forward / backward)
    }

    /// [definition] **The entropy coordinate of a cell as a ratio product**,
    /// `R(r) = Π_(i<r) P(i→i+1)/P(i+1→i)`; its log is `s(r)` (Lean `ChainAxes.coordinate`), the
    /// carry taken at the carry section.
    pub fn coordinate(&self, cell: usize) -> Result<Rat, ThermalError> {
        if cell >= self.cells() {
            return Err(ThermalError::Shape {
                what: "cell of the chain",
                expected: self.cells(),
                found: cell,
            });
        }
        let mut product = Rat::one();
        for junction in 0..cell {
            product *= self.affinity(junction)?;
        }
        Ok(product)
    }

    /// [proved-derived; implemented-exact] **The turn**: the cycle ratio product
    /// `Π_i P(i→i+1)/P(i+1→i)` of a ring, whose log is the cycle affinity; it does not depend on
    /// the law (Lean `cycleAffinity_law_free`). One on an open chain, which has no cycle.
    pub fn turn(&self) -> Result<Rat, ThermalError> {
        if !self.closed {
            return Ok(Rat::one());
        }
        let mut product = Rat::one();
        for junction in 0..self.cells() {
            product *= self.affinity(junction)?;
        }
        Ok(product)
    }

    /// The flows `J₊(i) = π(i) P(i→i+1)`, `J₋(i) = π(i+1) P(i+1→i)` of every junction at a law.
    pub fn junction_flows(&self, law: &[Rat]) -> Result<Vec<JunctionFlow>, ThermalError> {
        if law.len() != self.cells() {
            return Err(ThermalError::Shape {
                what: "law (one mass per cell)",
                expected: self.cells(),
                found: law.len(),
            });
        }
        (0..self.junctions())
            .map(|from| {
                let to = (from + 1) % self.cells();
                JunctionFlow::new(
                    &law[from] * self.chain.probability(from, to),
                    &law[to] * self.chain.probability(to, from),
                )
            })
            .collect()
    }

    /// [proved-derived; implemented-exact] **The current**: the one net flow every junction
    /// carries at a stationary law. Zero on an open chain (Lean `stationary_cut_balance`,
    /// `path_detailedBalance`); on a ring it has the sign of the cycle affinity
    /// (`current_affinity_sign`), and stationarity makes it one current (`ring_one_current`,
    /// `ring_nets_eq`).
    /// Refused at a law that is not stationary, `πP ≠ π` (on an open chain equal junction nets
    /// force the end cells to gain or lose), and when the junctions carry different net flows.
    pub fn current(&self, law: &[Rat]) -> Result<Rat, ThermalError> {
        let flows = self.junction_flows(law)?;
        for cell in 0..self.cells() {
            let reached: Rat = (0..self.cells())
                .map(|from| &law[from] * self.chain.probability(from, cell))
                .sum();
            if reached != law[cell] {
                return Err(ThermalError::NotStationary { cell });
            }
        }
        let current = flows[0].net();
        if let Some(junction) = flows.iter().position(|flow| flow.net() != current) {
            return Err(ThermalError::NotOneCurrent { junction });
        }
        Ok(current)
    }

    /// [proved-derived; implemented-exact] **The production per epoch** at a law: Schnakenberg's
    /// production across the chain's junctions ([`NeckProduction`], bits), which is the chain's
    /// [`MarkovChain::epoch_production`] at every law. At a stationary law of a ring it is the
    /// current times the cycle affinity, `J · log₂ turn` (Lean `ringProduction_eq_neck`,
    /// `neckProduction_ring_eq`, `stationary_ringProduction_eq`, `cycleAffinity_law_free`); at a
    /// stationary law of an open chain it is zero (`path_no_arrow`).
    pub fn production(&self, law: &[Rat]) -> Result<SymbolicSurprisal, ThermalError> {
        Ok(NeckProduction::across(self.junction_flows(law)?)?
            .production()
            .clone())
    }

    /// [proved-derived; implemented-exact] **The ring's production as current times affinity**,
    /// `J · log₂ turn`, at a stationary law (Lean `stationary_ringProduction_eq`, composing
    /// `ring_one_current` and `ringProduction_eq`); it equals [`Self::production`] there
    /// (`neckProduction_ring_eq`). Refused off a stationary law ([`Self::current`]).
    pub fn cycle_production(&self, law: &[Rat]) -> Result<SymbolicSurprisal, ThermalError> {
        Ok(SymbolicSurprisal::log2_of_ratio(&self.turn()?)?.scaled(&self.current(law)?))
    }

    /// [proved-derived; implemented-exact] **The two-axis reading of an aeon** of the chain: the
    /// signed epochs at the carry section, the heat and the entropy coordinate's change, which
    /// cross as `heat = (R(end)/R(start)) · turnⁿ` ([`TwoAxisReading::crosses`], Lean
    /// `entropy_reading`).
    pub fn axes(&self, aeon: &Aeon<MarkovChain>) -> Result<TwoAxisReading, ThermalError> {
        let carry = self.carry_section();
        let forward = epochs(aeon, |step: &Transition| *step == carry).flux();
        let backward = epochs(aeon, |step: &Transition| {
            step.from == carry.to && step.to == carry.from
        })
        .flux();
        let occurrences = aeon.occurrences();
        let start = occurrences[0];
        let end = occurrences[occurrences.len() - 1];
        Ok(TwoAxisReading {
            longitudinal: forward - backward,
            entropy: self.chain.heat(aeon)?,
            state: self.coordinate(end)? / self.coordinate(start)?,
            turn: self.turn()?,
        })
    }
}
