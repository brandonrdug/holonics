//! **Production: the arrow of an aeon, and the first return across grains.**
//!
//! [definition] Lean `Aeon/Production/PathReversal` and `Aeon/Production/Kac`, the aeon record
//! (A4–A6, A9). A finite Markov chain with rational transition probabilities is a parametric
//! complex ([`MarkovChain`]): its occurrences are the states, its passages the transitions of
//! positive probability. An aeon of `n` epochs is an [`Aeon`] of `n` transitions, and its
//! reversal `Rγ` is [`Aeon::reverse`]. Its law from a declared law `π` at the first occurrence is
//! `P_γ = π(γ₀) ∏ P(γᵢ, γᵢ₊₁)` (`pathLaw`).
//!
//! **Production is carried as the exact ratio product.** Log-ratios are not rational, so the
//! operand is the ratio `P_γ / P_(Rγ)` itself, whose logarithm is the aeon's production
//! ([`MarkovChain::production`]). It splits exactly into the state ratio `π(γ₀)/π(γₙ)`, read by the
//! two bounding occurrences, and the heat: the product of the step affinities
//! `P(x→y)/P(y→x)` ([`MarkovChain::heat`], `pathLogRatio_split`). On a cycle the state ratio is one
//! and the aeon reads its cycle affinity, which does not depend on `π`
//! (`cycle_logRatio_eq_affinity`). **Detailed balance holds exactly when every cycle's ratio
//! product is one** ([`MarkovChain::reversible_law`]): the affinity is then an exact
//! multiplicative clock, `π(y)/π(x)` (`detailedBalance_cycle_affinity_zero`).
//!
//! The mean production `σ_n = D(P_γ ‖ P_(Rγ)) = Σ_γ P_γ log₂(P_γ/P_(Rγ))` is carried as its exact
//! form in `log₂ p` ([`MarkovChain::mean_production`]), and for a stationary law it is `n` times
//! the epoch production `σ = Σ J(x,y) log₂(J(x,y)/J(y,x))`, zero exactly under detailed balance
//! (`production_eq_mul`, `production_eq_zero_iff`). The form is exact; its numeric enclosure is the
//! exterior face.
//!
//! **Kac.** A section `A` of states is a coarser receiver whose ticks are the returns to it. The
//! mean first return solves the first-step equations `m = 1 + Σ_(z∉A) P(·,z) m(z)` exactly
//! ([`MarkovChain::mean_return`], `firstReturn_existsUnique`), and for the stationary law
//! `π(x) · m_x(x) = 1` (`kac_single_state`, `kac_hasSum`); across grains the mean number of fine
//! epochs per coarse epoch is the undivided pair `(π(S) : π(A))` ([`MarkovChain::grain_ratio`],
//! `kac_grain_ratio`).
//!
//! **Abramov.** One coarse epoch's word (the path until the return to `A`) carries the entropy of
//! its first step plus, where that step avoids `A`, the entropy of the rest: `H = h + avoid_A H`
//! with `h(y) = −Σ_z P(y,z) log₂ P(y,z)` ([`MarkovChain::epoch_entropy`],
//! [`MarkovChain::word_entropy`], `Kac.wordEntropy_succ`, `wordEntropy_eq_sum`). Kac's lemma for
//! the observable `h` then gives Abramov's formula for the induced chain: from the section's
//! stationary weights the word entropy is the undivided pair `(Σ_y π(y) h(y) : π(A))`, the fine
//! entropy per coarse epoch, `h(T_A) = h(T)/μ(A)` ([`MarkovChain::abramov`], `Kac.abramov`,
//! `abramov_ledger`). Every entropy is the exact form in `log₂ p`, solved coordinate by
//! coordinate.
//!
//! [open] The converse of Kolmogorov's criterion (every cycle ratio product one ⇒ detailed
//! balance), decided here through the fundamental cycles of a spanning tree, is owed in Lean
//! (#62).

use std::collections::VecDeque;
use std::convert::Infallible;

use num_traits::{One, Signed, Zero};

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ParametricComplex, Step};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{at, matrix};
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{Presentation, Rat};

/// [definition] **A transition** `from → to` of positive probability: a passage of the chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Transition {
    pub from: usize,
    pub to: usize,
}

/// [definition] **The entropy of a coarse epoch's word from a section**, undivided: the stationary
/// weighted word entropy `Σ_(y∈A) π(y) H(y)` (bits, exact in `log₂ p`) against the section's mass
/// `π(A)` ([`MarkovChain::abramov`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionEntropy {
    pub entropy: SymbolicSurprisal,
    pub mass: Rat,
}

/// [definition] **A finite Markov chain** with exact rational transition probabilities: nonnegative
/// rows of total mass one (Lean `Kac.Stochastic`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MarkovChain {
    transitions: ExactRatMatrix,
}

impl ParametricComplex for MarkovChain {
    type Occurrence = usize;
    type Passage = Transition;
    type Cell = Infallible;

    fn ends(&self, passage: &Transition) -> Option<(usize, usize)> {
        let probability = self.transitions.get(passage.from, passage.to).ok()?;
        probability
            .is_positive()
            .then_some((passage.from, passage.to))
    }

    fn cell(&self, cell: &Infallible) -> Option<(usize, Vec<Step<Transition>>)> {
        match *cell {}
    }
}

impl MarkovChain {
    /// A stochastic matrix, refused at the first row that is not a probability law.
    pub fn new(transitions: ExactRatMatrix) -> Result<Self, AeonError> {
        if !transitions.is_square() {
            return Err(AeonError::Shape {
                what: "square transition matrix",
                expected: transitions.rows(),
                found: transitions.columns(),
            });
        }
        for state in 0..transitions.rows() {
            let row = transitions.row(state)?;
            if row.iter().any(Signed::is_negative) {
                return Err(AeonError::NotStochastic {
                    state,
                    reason: "a negative probability",
                });
            }
            if row.iter().sum::<Rat>() != Rat::one() {
                return Err(AeonError::NotStochastic {
                    state,
                    reason: "total mass is not one",
                });
            }
        }
        Ok(Self { transitions })
    }

    pub fn states(&self) -> usize {
        self.transitions.rows()
    }

    /// `P(from, to)`.
    pub fn probability(&self, from: usize, to: usize) -> Rat {
        at(&self.transitions, from, to)
    }

    /// The aeon visiting `states` in order, one transition per epoch.
    pub fn walk(&self, states: &[usize]) -> Result<Aeon<Self>, AeonError> {
        let start = *states.first().ok_or(AeonError::Shape {
            what: "states of an aeon",
            expected: 1,
            found: 0,
        })?;
        let steps = states
            .windows(2)
            .map(|pair| {
                Step::along(Transition {
                    from: pair[0],
                    to: pair[1],
                })
            })
            .collect();
        Aeon::new(self, start, steps)
    }

    /// [definition] **The law of an aeon**: `π(γ₀) ∏ P(γᵢ, γᵢ₊₁)` over its occurrences. Lean
    /// `pathLaw`; the reversed aeon's law is Lean `revLaw` (`pathLaw_reversal`).
    pub fn path_law(&self, law: &[Rat], aeon: &Aeon<Self>) -> Result<Rat, AeonError> {
        self.check_law(law)?;
        let occurrences = aeon.occurrences();
        let mut probability = law[occurrences[0]].clone();
        for pair in occurrences.windows(2) {
            probability *= self.probability(pair[0], pair[1]);
        }
        Ok(probability)
    }

    /// [definition] **The production of an aeon as its exact ratio product** `P_γ / P_(Rγ)`, whose
    /// logarithm is the aeon's production. Refused at the first step with no reverse transition
    /// (Lean `Admissible.support`).
    pub fn production(&self, law: &[Rat], aeon: &Aeon<Self>) -> Result<Rat, AeonError> {
        // The heat names the first step with no reverse transition before the laws are divided.
        self.heat(aeon)?;
        let reversed = self.path_law(law, &aeon.reverse())?;
        if reversed.is_zero() {
            return Err(AeonError::NotAPositiveLaw {
                reason: "the law vanishes at the aeon's last occurrence",
            });
        }
        Ok(self.path_law(law, aeon)? / reversed)
    }

    /// [definition] **The heat of an aeon**: the product of its step affinities
    /// `P(x→y)/P(y→x)`, read by the medium. Lean `affinity`, summed in the additive chart.
    pub fn heat(&self, aeon: &Aeon<Self>) -> Result<Rat, AeonError> {
        let mut product = Rat::one();
        for pair in aeon.occurrences().windows(2) {
            product *= self.affinity(pair[0], pair[1])?;
        }
        Ok(product)
    }

    /// The affinity ratio `P(x→y)/P(y→x)` of one step.
    fn affinity(&self, from: usize, to: usize) -> Result<Rat, AeonError> {
        let back = self.probability(to, from);
        if back.is_zero() {
            return Err(AeonError::IrreversibleStep { from, to });
        }
        Ok(self.probability(from, to) / back)
    }

    /// [definition] **The reversible law**, when the chain is in detailed balance: the unique law
    /// `π` of total mass one with `π(x) P(x,y) = π(y) P(y,x)` on every pair. It is read along a
    /// spanning tree of the support from state `0` (`π(y)/π(x) = P(x→y)/P(y→x)`), and every
    /// passage off the tree closes a fundamental cycle whose ratio product must be one; the first
    /// that is not is returned as the obstruction. Refused when the support is not symmetric or not
    /// connected.
    pub fn reversible_law(&self) -> Result<Vec<Rat>, AeonError> {
        let n = self.states();
        if n == 0 {
            return Err(AeonError::NotIrreducible { state: 0 });
        }
        let mut weight: Vec<Option<Rat>> = vec![None; n];
        let mut parent: Vec<Option<usize>> = vec![None; n];
        weight[0] = Some(Rat::one());
        let mut queue = VecDeque::from([0usize]);
        while let Some(x) = queue.pop_front() {
            for y in 0..n {
                if y == x || self.probability(x, y).is_zero() || weight[y].is_some() {
                    continue;
                }
                let ratio = self.affinity(x, y)?;
                weight[y] = Some(weight[x].clone().expect("a queued state is weighted") * ratio);
                parent[y] = Some(x);
                queue.push_back(y);
            }
        }
        let weight: Vec<Rat> = weight
            .into_iter()
            .enumerate()
            .map(|(state, value)| value.ok_or(AeonError::NotIrreducible { state }))
            .collect::<Result<_, _>>()?;
        for x in 0..n {
            for y in 0..n {
                if x == y || self.probability(x, y).is_zero() {
                    continue;
                }
                let affinity = self.affinity(x, y)?;
                let product = &weight[x] * &affinity / &weight[y];
                if !product.is_one() {
                    // 0 → … → x → y → … → 0: the fundamental cycle of the passage x → y.
                    let mut states = tree_path(&parent, x);
                    states.reverse();
                    states.extend(tree_path(&parent, y));
                    return Err(AeonError::CycleObstruction {
                        cycle: states,
                        product,
                    });
                }
            }
        }
        let total: Rat = weight.iter().sum();
        Ok(weight.into_iter().map(|value| value / &total).collect())
    }

    /// [definition] **The stationary law**: the unique law of total mass one with `π P = π`.
    /// Refused when it is not unique.
    pub fn stationary_law(&self) -> Result<Vec<Rat>, AeonError> {
        let n = self.states();
        let system = matrix(n + 1, n, |row, column| {
            if row == n {
                Rat::one()
            } else {
                let identity = if row == column {
                    Rat::one()
                } else {
                    Rat::zero()
                };
                self.probability(column, row) - identity
            }
        })?;
        let mut target = vec![Rat::zero(); n];
        target.push(Rat::one());
        match system.preimage_fibre(&target)? {
            Some((law, kernel)) if kernel.is_empty() => Ok(law),
            Some((_, kernel)) => Err(AeonError::NotUnique {
                what: "stationary law",
                free: kernel.len(),
            }),
            None => Err(AeonError::NotAPositiveLaw {
                reason: "no stationary law of total mass one",
            }),
        }
    }

    /// [definition] **The mean first return to a section** `A`: the solution of the first-step
    /// equations `m(y) = 1 + Σ_(z∉A) P(y,z) m(z)` (Lean `FirstReturnEquations`), found by one exact
    /// solve. Refused when they have no solution (the chain is reducible off the section, Lean
    /// `Reducible.reducible_kac_fails`) or several, and when the section repeats a state.
    pub fn mean_return(&self, section: &[usize]) -> Result<Vec<Rat>, AeonError> {
        self.first_step(
            section,
            &vec![Rat::one(); self.states()],
            "mean first return",
        )
    }

    /// The first-step solution `m = f + avoid_A m` of an observable `f` (Lean
    /// `FirstReturnEquations P A f m`), by one exact solve.
    fn first_step(
        &self,
        section: &[usize],
        observable: &[Rat],
        what: &'static str,
    ) -> Result<Vec<Rat>, AeonError> {
        let n = self.states();
        if section.is_empty() || section.iter().any(|state| *state >= n) {
            return Err(AeonError::EmptySection);
        }
        // A section is a set: a repeated state would be counted twice in its stationary mass and
        // in every section sum read from this solution.
        if let Some(position) =
            (1..section.len()).find(|position| section[..*position].contains(&section[*position]))
        {
            return Err(AeonError::RepeatedState {
                state: section[position],
            });
        }
        let system = matrix(n, n, |y, z| {
            let identity = if y == z { Rat::one() } else { Rat::zero() };
            if section.contains(&z) {
                identity
            } else {
                identity - self.probability(y, z)
            }
        })?;
        match system.preimage_fibre(observable)? {
            Some((solution, kernel)) if kernel.is_empty() => Ok(solution),
            Some((_, kernel)) => Err(AeonError::NotUnique {
                what,
                free: kernel.len(),
            }),
            None => Err(AeonError::NoFirstReturn),
        }
    }

    /// [definition] **The entropy of one fine epoch** from each state,
    /// `h(y) = −Σ_z P(y,z) log₂ P(y,z)`, as its exact form in `log₂ p`. Lean `Kac.epochEntropy`
    /// (in bits).
    pub fn epoch_entropy(&self) -> Result<Vec<SymbolicSurprisal>, AeonError> {
        (0..self.states())
            .map(|y| {
                let mut entropy = SymbolicSurprisal::zero();
                for z in 0..self.states() {
                    let probability = self.probability(y, z);
                    if probability.is_positive() {
                        entropy = entropy.plus(
                            &SymbolicSurprisal::of_probability(&probability)?.scaled(&probability),
                        );
                    }
                }
                Ok(entropy)
            })
            .collect()
    }

    /// [definition] **The entropy of one coarse epoch's word** from each state: the first-step
    /// solution `H = h + avoid_A H` of the fine entropy, the limit of the stopped words' entropies
    /// `H_N = Σ_(n<N) avoid_Aⁿ h` (Lean `Kac.wordEntropy_succ`, `wordEntropy_eq_sum`). The
    /// equations have rational coefficients, so each `log₂ p` coordinate is solved exactly on its
    /// own; refused as the mean first return is.
    pub fn word_entropy(&self, section: &[usize]) -> Result<Vec<SymbolicSurprisal>, AeonError> {
        self.mean_return(section)?;
        let fine = self.epoch_entropy()?;
        let primes: std::collections::BTreeSet<u64> = fine
            .iter()
            .flat_map(|entropy| entropy.terms().keys().copied())
            .collect();
        let mut word = vec![SymbolicSurprisal::zero(); self.states()];
        for prime in primes {
            let coordinate: Vec<Rat> = fine
                .iter()
                .map(|entropy| entropy.terms().get(&prime).cloned().unwrap_or_default())
                .collect();
            let solved = self.first_step(section, &coordinate, "coarse word entropy")?;
            for (entropy, coefficient) in word.iter_mut().zip(solved) {
                *entropy = entropy.plus(&SymbolicSurprisal::term(prime, coefficient)?);
            }
        }
        Ok(word)
    }

    /// [proved-derived; implemented-exact] **Abramov's formula for the induced chain**: the entropy
    /// of one coarse epoch's word read from the section's stationary weights, kept as the undivided
    /// pair `(Σ_(y∈A) π(y) H(y) : π(A))`. By Kac's lemma for the observable `h` its first entry is
    /// the fine entropy `Σ_y π(y) h(y)` exactly (`Kac.kac_ledger_observable`), so per coarse epoch
    /// it is `h(T)/μ(A)` (Lean `Kac.abramov`, the limit of `abramov_ledger`). Refused when the
    /// section carries no stationary mass or repeats a state ([`AeonError::RepeatedState`]).
    pub fn abramov(&self, section: &[usize]) -> Result<SectionEntropy, AeonError> {
        let law = self.stationary_law()?;
        let word = self.word_entropy(section)?;
        let mass: Rat = section.iter().map(|state| law[*state].clone()).sum();
        if mass.is_zero() {
            return Err(AeonError::EmptySection);
        }
        let entropy = section
            .iter()
            .fold(SymbolicSurprisal::zero(), |sum, state| {
                sum.plus(&word[*state].scaled(&law[*state]))
            });
        Ok(SectionEntropy { entropy, mass })
    }

    /// [definition] **Kac across grains**: the mean number of fine epochs per coarse epoch of the
    /// section `A`, from the stationary law restricted to `A`, as the undivided pair
    /// `(Σ_(y∈A) π(y) m(y) : π(A))`. By Kac it equals `(π(S) : π(A))`. Refused when the section
    /// carries no stationary mass or repeats a state ([`AeonError::RepeatedState`]).
    pub fn grain_ratio(&self, section: &[usize]) -> Result<Presentation, AeonError> {
        let law = self.stationary_law()?;
        let mean = self.mean_return(section)?;
        let mass: Rat = section.iter().map(|state| law[*state].clone()).sum();
        if mass.is_zero() {
            return Err(AeonError::EmptySection);
        }
        let returned: Rat = section
            .iter()
            .map(|state| &law[*state] * &mean[*state])
            .sum();
        Ok(Presentation::new(returned, mass))
    }

    /// [definition] **The epoch production** `σ = Σ_(x,y) J(x,y) log₂(J(x,y)/J(y,x))`,
    /// `J(x,y) = π(x) P(x,y)`, as its exact form in `log₂ p`. Lean `epochProduction` (in bits).
    pub fn epoch_production(&self, law: &[Rat]) -> Result<SymbolicSurprisal, AeonError> {
        self.check_law(law)?;
        let mut production = SymbolicSurprisal::zero();
        for x in 0..self.states() {
            for y in 0..self.states() {
                let flow = &law[x] * self.probability(x, y);
                if flow.is_zero() {
                    continue;
                }
                let back = &law[y] * self.probability(y, x);
                if back.is_zero() {
                    return Err(AeonError::IrreversibleStep { from: x, to: y });
                }
                production = production
                    .plus(&SymbolicSurprisal::log2_of_ratio(&(&flow / back))?.scaled(&flow));
            }
        }
        Ok(production)
    }

    /// [definition] **The mean production of aeons of `epochs` epochs**,
    /// `σ_n = D(P_γ ‖ P_(Rγ)) = Σ_γ P_γ log₂(P_γ/P_(Rγ))`, over every aeon of positive law, as its
    /// exact form in `log₂ p`. Lean `production` (in bits). The aeons are enumerated, `|S|^(n+1)`
    /// at most.
    pub fn mean_production(
        &self,
        law: &[Rat],
        epochs: usize,
    ) -> Result<SymbolicSurprisal, AeonError> {
        self.check_law(law)?;
        let mut production = SymbolicSurprisal::zero();
        let mut frontier: Vec<Vec<usize>> = (0..self.states())
            .filter(|state| law[*state].is_positive())
            .map(|state| vec![state])
            .collect();
        for _ in 0..epochs {
            frontier = frontier
                .into_iter()
                .flat_map(|states| {
                    let last = states[states.len() - 1];
                    (0..self.states())
                        .filter(move |next| self.probability(last, *next).is_positive())
                        .map(move |next| {
                            let mut extended = states.clone();
                            extended.push(next);
                            extended
                        })
                })
                .collect();
        }
        for states in frontier {
            let aeon = self.walk(&states)?;
            let probability = self.path_law(law, &aeon)?;
            production = production.plus(
                &SymbolicSurprisal::log2_of_ratio(&self.production(law, &aeon)?)?
                    .scaled(&probability),
            );
        }
        Ok(production)
    }

    fn check_law(&self, law: &[Rat]) -> Result<(), AeonError> {
        if law.len() != self.states() {
            return Err(AeonError::Shape {
                what: "law (one mass per state)",
                expected: self.states(),
                found: law.len(),
            });
        }
        if law.iter().any(Signed::is_negative) {
            return Err(AeonError::NotAPositiveLaw {
                reason: "a negative mass",
            });
        }
        Ok(())
    }
}

/// The states from the tree's root `0` down to `state`, root last.
fn tree_path(parent: &[Option<usize>], state: usize) -> Vec<usize> {
    let mut path = vec![state];
    let mut current = state;
    while let Some(up) = parent[current] {
        path.push(up);
        current = up;
    }
    path
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn chain(rows: &[[Rat; 3]; 3]) -> MarkovChain {
        MarkovChain::new(
            ExactRatMatrix::new(rows.iter().map(|row| row.to_vec()).collect()).unwrap(),
        )
        .unwrap()
    }

    /// Conductances `c(0,1)=1, c(1,2)=2, c(0,2)=1, c(2,2)=1`: reversible for `π = (2,3,4)/9`.
    fn reversible() -> MarkovChain {
        chain(&[
            [integer(0), rat(1, 2), rat(1, 2)],
            [rat(1, 3), integer(0), rat(2, 3)],
            [rat(1, 4), rat(1, 2), rat(1, 4)],
        ])
    }

    /// The biased rotation of three states, `2/3` forward and `1/3` back (Lean `Rotation.P`).
    fn rotation() -> MarkovChain {
        chain(&[
            [integer(0), rat(2, 3), rat(1, 3)],
            [rat(1, 3), integer(0), rat(2, 3)],
            [rat(2, 3), rat(1, 3), integer(0)],
        ])
    }

    /// **The production of an aeon is state times heat.** `P_γ/P_(Rγ)` is exactly the state
    /// ratio `π(γ₀)/π(γₙ)` times the product of the step affinities, for any positive law; on a
    /// cycle it is the cycle affinity, the same for every law. Lean
    /// `PathReversal.pathLogRatio_split`, `cycle_logRatio_eq_affinity`.
    #[test]
    fn the_production_of_an_aeon_is_state_times_heat() {
        let laws = [
            vec![rat(1, 3), rat(1, 3), rat(1, 3)],
            vec![rat(1, 2), rat(1, 5), rat(3, 10)],
        ];
        for chain in [reversible(), rotation()] {
            let open = chain.walk(&[0, 1, 2, 1, 0, 2]).unwrap();
            let cycle = chain.walk(&[1, 2, 0, 2, 0, 1]).unwrap();
            for law in &laws {
                let state = &law[*open.start()] / &law[*open.end()];
                assert_eq!(
                    chain.production(law, &open).unwrap(),
                    state * chain.heat(&open).unwrap()
                );
                assert_eq!(
                    chain.production(law, &cycle).unwrap(),
                    chain.heat(&cycle).unwrap()
                );
            }
        }
    }

    /// **Detailed balance holds exactly when every cycle's ratio product is one.** The reversible
    /// chain's law is read along a spanning tree, is its stationary law and balances every pair,
    /// and its cycles read one; the biased rotation is refused with its fundamental cycle, whose
    /// ratio product is `2³` (affinity `3 log 2`). Lean
    /// `PathReversal.detailedBalance_cycle_affinity_zero` (the forward direction),
    /// `Rotation.rotation_cycle_affinity`; the converse is owed (#62).
    #[test]
    fn detailed_balance_is_every_cycle_reading_one() {
        let balanced = reversible();
        let law = balanced.reversible_law().unwrap();
        assert_eq!(law, vec![rat(2, 9), rat(3, 9), rat(4, 9)]);
        assert_eq!(balanced.stationary_law().unwrap(), law);
        for x in 0..3 {
            for y in 0..3 {
                assert_eq!(
                    &law[x] * balanced.probability(x, y),
                    &law[y] * balanced.probability(y, x)
                );
            }
        }
        for states in [&[0usize, 1, 2, 0][..], &[0, 2, 1, 0], &[2, 2, 1, 0, 1, 2]] {
            assert!(
                balanced
                    .heat(&balanced.walk(states).unwrap())
                    .unwrap()
                    .is_one()
            );
        }
        let biased = rotation();
        match biased.reversible_law() {
            Err(AeonError::CycleObstruction { cycle, product }) => {
                let aeon = biased.walk(&cycle).unwrap();
                assert_eq!(aeon.start(), aeon.end());
                assert_eq!(biased.heat(&aeon).unwrap(), product);
                assert!(product == integer(8) || product == rat(1, 8));
            }
            other => panic!("the rotation is not reversible: {other:?}"),
        }
        assert_eq!(
            biased.heat(&biased.walk(&[0, 1, 2, 0]).unwrap()).unwrap(),
            integer(8)
        );
    }

    /// **Production is the relative entropy of an aeon against its reversal.** For a stationary
    /// law, `σ_n = n σ` exactly as a form in `log₂ p`; `σ = 0` exactly under detailed balance, and
    /// the biased rotation produces `σ = (1/3) log₂ 2` per epoch. Lean
    /// `PathReversal.production_eq_mul`, `production_eq_zero_iff`, `epochProduction_eq_zero_iff`,
    /// `Rotation.rotation_production_pos` (`(ln 2)/3` nats).
    #[test]
    fn production_is_the_relative_entropy_against_the_reversal() {
        let biased = rotation();
        let uniform = biased.stationary_law().unwrap();
        let sigma = biased.epoch_production(&uniform).unwrap();
        assert_eq!(sigma, SymbolicSurprisal::term(2, rat(1, 3)).unwrap());
        for epochs in 0..4usize {
            assert_eq!(
                biased.mean_production(&uniform, epochs).unwrap(),
                sigma.scaled(&integer(epochs as i64))
            );
        }
        let balanced = reversible();
        let law = balanced.stationary_law().unwrap();
        assert!(balanced.epoch_production(&law).unwrap().is_zero());
        for epochs in 1..4usize {
            assert!(balanced.mean_production(&law, epochs).unwrap().is_zero());
        }
    }

    /// **Kac: the mean return time is `1/π(x)`, exactly.** The first-step equations have one
    /// solution, `π(x) · m_x(x) = 1` for every state, and across grains the mean number of fine
    /// epochs per coarse epoch is `(π(S) : π(A))`. Lean `Kac.firstReturn_existsUnique`,
    /// `kac_single_state`, `kac_hasSum`, `kac_grain_ratio`.
    #[test]
    fn the_mean_return_time_is_the_reciprocal_stationary_mass() {
        for chain in [reversible(), rotation()] {
            let law = chain.stationary_law().unwrap();
            for x in 0..3 {
                let mean = chain.mean_return(&[x]).unwrap();
                assert_eq!(&law[x] * &mean[x], Rat::one());
            }
            for section in [&[0usize, 1][..], &[2], &[0, 1, 2]] {
                let mass: Rat = section.iter().map(|state| law[*state].clone()).sum();
                assert!(
                    chain
                        .grain_ratio(section)
                        .unwrap()
                        .projectively_equal(&Presentation::new(Rat::one(), mass))
                );
            }
        }
    }

    /// `Σ_(y∈A) π(y) f(y)` for a symbolic observable.
    fn weighted(law: &[Rat], states: &[usize], f: &[SymbolicSurprisal]) -> SymbolicSurprisal {
        states.iter().fold(SymbolicSurprisal::zero(), |sum, y| {
            sum.plus(&f[*y].scaled(&law[*y]))
        })
    }

    /// One fine epoch that avoids the section: `(avoid_A g)(y) = Σ_(z∉A) P(y,z) g(z)`.
    fn avoid(
        chain: &MarkovChain,
        section: &[usize],
        g: &[SymbolicSurprisal],
    ) -> Vec<SymbolicSurprisal> {
        (0..chain.states())
            .map(|y| {
                (0..chain.states())
                    .filter(|z| !section.contains(z))
                    .fold(SymbolicSurprisal::zero(), |sum, z| {
                        sum.plus(&g[z].scaled(&chain.probability(y, z)))
                    })
            })
            .collect()
    }

    /// The laws of the words of one coarse epoch from `y`, stopped at `horizon` fine epochs (Lean
    /// `Kac.wordLaw`): the path ends on reaching the section.
    fn word_laws(chain: &MarkovChain, section: &[usize], y: usize, horizon: usize) -> Vec<Rat> {
        if horizon == 0 {
            return vec![Rat::one()];
        }
        (0..chain.states())
            .filter(|z| chain.probability(y, *z).is_positive())
            .flat_map(|z| {
                let step = chain.probability(y, z);
                if section.contains(&z) {
                    vec![step]
                } else {
                    word_laws(chain, section, z, horizon - 1)
                        .into_iter()
                        .map(|law| &step * law)
                        .collect()
                }
            })
            .collect()
    }

    /// **Abramov's formula for the induced chain.** The word entropy solves `H = h + avoid_A H`;
    /// the entropy of the words stopped at `N` fine epochs, enumerated from their laws, is
    /// `Σ_(n<N) avoid_Aⁿ h`, and its stationary section weight is the fine entropy minus the
    /// entropy still avoiding the section, exactly at every `N`; in the limit the section's word
    /// entropy is the fine entropy `Σ π h`, per `π(A)`. Lean `Kac.wordEntropy_succ`,
    /// `wordEntropy_eq_sum`, `abramov_ledger`, `abramov`.
    #[test]
    fn the_coarse_word_entropy_is_the_fine_entropy_per_section_mass() {
        for chain in [reversible(), rotation()] {
            let law = chain.stationary_law().unwrap();
            let fine = chain.epoch_entropy().unwrap();
            let all: Vec<usize> = (0..3).collect();
            let rate = weighted(&law, &all, &fine);
            assert!(!rate.is_zero());
            for section in [&[0usize][..], &[0, 1], &[2], &[0, 1, 2]] {
                let word = chain.word_entropy(section).unwrap();
                let stepped = avoid(&chain, section, &word);
                for y in 0..3 {
                    assert_eq!(word[y], fine[y].plus(&stepped[y]));
                }
                let mut power = fine.clone();
                let mut truncated = vec![SymbolicSurprisal::zero(); 3];
                for horizon in 0..5 {
                    for y in 0..3 {
                        let enumerated = word_laws(&chain, section, y, horizon).iter().fold(
                            SymbolicSurprisal::zero(),
                            |sum, p| {
                                sum.plus(&SymbolicSurprisal::of_probability(p).unwrap().scaled(p))
                            },
                        );
                        assert_eq!(enumerated, truncated[y]);
                    }
                    assert_eq!(
                        weighted(&law, section, &truncated),
                        rate.minus(&weighted(&law, &all, &power))
                    );
                    truncated = truncated
                        .iter()
                        .zip(&power)
                        .map(|(sum, term)| sum.plus(term))
                        .collect();
                    power = avoid(&chain, section, &power);
                }
                let mass: Rat = section.iter().map(|y| law[*y].clone()).sum();
                assert_eq!(
                    chain.abramov(section).unwrap(),
                    SectionEntropy {
                        entropy: rate.clone(),
                        mass
                    }
                );
            }
        }
    }

    /// [counterexample] **A section that repeats a state is refused.** Read as a list, `[0, 0]`
    /// would weigh state `0` twice: the grain ratio `(2 : 4/9)` in place of `(1 : 2/9)` and the
    /// Abramov mass `4/9` in place of `2/9`. A section is a set of states.
    #[test]
    fn a_section_that_repeats_a_state_is_refused() {
        let chain = reversible();
        let refusals = |section: &[usize]| {
            (
                chain.grain_ratio(section).err(),
                chain.abramov(section).err(),
            )
        };
        for (section, state) in [(&[0usize, 0][..], 0), (&[2, 1, 2], 2)] {
            let refused = Some(AeonError::RepeatedState { state });
            assert_eq!(refusals(section), (refused.clone(), refused));
        }
        assert!(
            chain
                .grain_ratio(&[0])
                .unwrap()
                .projectively_equal(&Presentation::new(Rat::one(), rat(2, 9)))
        );
    }

    /// [counterexample] **Kac fails without irreducibility.** The identity chain on two states
    /// never leaves state `1`, so the first-step equations of the return to `0` have no solution.
    /// Lean `Kac.Reducible.reducible_kac_fails`.
    #[test]
    fn a_reducible_chain_has_no_first_return() {
        let stay = MarkovChain::new(ExactRatMatrix::identity(2).unwrap()).unwrap();
        assert_eq!(stay.mean_return(&[0]), Err(AeonError::NoFirstReturn));
    }
}
