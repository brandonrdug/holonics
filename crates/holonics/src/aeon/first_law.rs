//! **The first law of learning.**
//!
//! [definition] Lean `Aeon/Production/FirstLaw` and the aeon record (A7). Along an aeon a source
//! law `p` (what arrives) and a receiver law `q` (what the constitution predicts) both move: they
//! are functions of the occurrence the motion has reached. Their cross-entropy
//! `C(p, q) = −Σ pᵢ log₂ qᵢ` changes over one step from `(p, q)` to `(p′, q′)` by
//!
//! ```text
//! exchange     −Σ (p′ᵢ − pᵢ) log₂ qᵢ          the source's flux through the unchanged receiver
//! deposition   −Σ p′ᵢ (log₂ q′ᵢ − log₂ qᵢ)     the change of the constitution's contribution
//! ```
//!
//! and `C(p′, q′) − C(p, q) = exchange + deposition` exactly (`first_law_epoch`). Every term is an
//! exact ℚ-linear form in `log₂ p` ([`SymbolicSurprisal`]), so the law is an identity of forms
//! decided coefficientwise, with no logarithm evaluated. Along an aeon the steps telescope
//! (`first_law_aeon`): the sum depends only on the two bounding occurrences, and over a cycle
//! exchange is minus deposition (`cycle_exchange_eq_neg_deposition`). Each term alone depends on
//! the path: exchange and deposition are 1-forms that are not closed, while their sum is the exact
//! form `dC` (`exchange_is_path_dependent`).

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ParametricComplex};
use crate::ratio::Rat;
use crate::ratio::surprisal::SymbolicSurprisal;
use num_traits::{One, Signed};

/// [definition] **A finite positive law**: rational masses, each positive, of total mass one.
/// Lean `PositiveProbabilitySection`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PositiveLaw {
    masses: Vec<Rat>,
}

impl PositiveLaw {
    pub fn new(masses: Vec<Rat>) -> Result<Self, AeonError> {
        if masses.iter().any(|mass| !mass.is_positive()) {
            return Err(AeonError::NotAPositiveLaw {
                reason: "a mass that is not positive",
            });
        }
        if masses.iter().sum::<Rat>() != Rat::one() {
            return Err(AeonError::NotAPositiveLaw {
                reason: "total mass is not one",
            });
        }
        Ok(Self { masses })
    }

    pub fn masses(&self) -> &[Rat] {
        &self.masses
    }

    /// [definition] **The cross-entropy** `C(p, q) = Σ pᵢ S(qᵢ)` of this source law received
    /// through `receiver`, in bits, as its exact form. Lean
    /// `Foundation/InformationReceiver.PositiveProbabilitySection.crossEntropy`.
    pub fn cross_entropy(&self, receiver: &Self) -> Result<SymbolicSurprisal, AeonError> {
        weighted_surprisal(&self.masses, receiver)
    }
}

/// `Σ wᵢ S(qᵢ)` for any rational weights: the owner of the weighted surprisal that exchange,
/// deposition and cross-entropy share, and of the infinitesimal exchange of a population's rate
/// (`physics::information::cross_entropy_rate`).
pub(crate) fn weighted_surprisal(
    weights: &[Rat],
    receiver: &PositiveLaw,
) -> Result<SymbolicSurprisal, AeonError> {
    if weights.len() != receiver.masses.len() {
        return Err(AeonError::Shape {
            what: "law extents",
            expected: receiver.masses.len(),
            found: weights.len(),
        });
    }
    let mut form = SymbolicSurprisal::zero();
    for (weight, mass) in weights.iter().zip(&receiver.masses) {
        form = form.plus(&SymbolicSurprisal::of_probability(mass)?.scaled(weight));
    }
    Ok(form)
}

/// [definition] **Exchange**: the source moves from `p` to `p′` through the unchanged receiver
/// `q`, `Σ (p′ᵢ − pᵢ) S(qᵢ)`. Lean `FirstLaw.exchange`.
pub fn exchange(
    source: &PositiveLaw,
    arrived: &PositiveLaw,
    receiver: &PositiveLaw,
) -> Result<SymbolicSurprisal, AeonError> {
    if source.masses.len() != arrived.masses.len() {
        return Err(AeonError::Shape {
            what: "law extents",
            expected: source.masses.len(),
            found: arrived.masses.len(),
        });
    }
    let moved: Vec<Rat> = arrived
        .masses
        .iter()
        .zip(&source.masses)
        .map(|(after, before)| after - before)
        .collect();
    weighted_surprisal(&moved, receiver)
}

/// [definition] **Deposition**: the receiver moves from `q` to `q′` at the arrived source `p′`,
/// `Σ p′ᵢ (S(q′ᵢ) − S(qᵢ))`. Lean `FirstLaw.deposition`.
pub fn deposition(
    arrived: &PositiveLaw,
    receiver: &PositiveLaw,
    deposited: &PositiveLaw,
) -> Result<SymbolicSurprisal, AeonError> {
    Ok(arrived
        .cross_entropy(deposited)?
        .minus(&arrived.cross_entropy(receiver)?))
}

/// [definition] **The learning balance of an aeon**: its summed exchange and deposition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LearningBalance {
    pub exchange: SymbolicSurprisal,
    pub deposition: SymbolicSurprisal,
}

impl LearningBalance {
    /// `exchange + deposition`: the change of cross-entropy between the bounding occurrences.
    pub fn total(&self) -> SymbolicSurprisal {
        self.exchange.plus(&self.deposition)
    }
}

/// [definition] **The first law along an aeon**: the source and receiver laws `laws(o) = (p, q)`
/// at each occurrence, and the exchange and deposition summed over the aeon's steps. Lean
/// `FirstLaw.first_law_aeon`.
pub fn learning_balance<K: ParametricComplex>(
    aeon: &Aeon<K>,
    laws: impl Fn(&K::Occurrence) -> Result<(PositiveLaw, PositiveLaw), AeonError>,
) -> Result<LearningBalance, AeonError> {
    let mut balance = LearningBalance {
        exchange: SymbolicSurprisal::zero(),
        deposition: SymbolicSurprisal::zero(),
    };
    let mut before = laws(aeon.start())?;
    for occurrence in aeon.occurrences().iter().skip(1) {
        let after = laws(occurrence)?;
        balance.exchange = balance
            .exchange
            .plus(&exchange(&before.0, &after.0, &before.1)?);
        balance.deposition = balance
            .deposition
            .plus(&deposition(&after.0, &before.1, &after.1)?);
        before = after;
    }
    Ok(balance)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::groupoid::ClockLift;
    use crate::ratio::rat;
    use num_bigint::{BigInt, BigUint};
    use num_traits::ToPrimitive;

    fn two_point(mass: Rat) -> PositiveLaw {
        PositiveLaw::new(vec![mass.clone(), Rat::one() - mass]).unwrap()
    }

    /// The source moves along navigator `0`'s lattice coordinate and the receiver along
    /// navigator `1`'s: `p = (1/2, 1/4, 1/5)[x₀]`, `q = (1/2, 1/3, 3/7)[x₁]` on the true side.
    fn grid_laws(point: &Vec<BigInt>) -> Result<(PositiveLaw, PositiveLaw), AeonError> {
        let sources = [rat(1, 2), rat(1, 4), rat(1, 5)];
        let receivers = [rat(1, 2), rat(1, 3), rat(3, 7)];
        let index = |coordinate: &BigInt, extent: usize| {
            coordinate.to_usize().filter(|index| *index < extent).ok_or(
                AeonError::NotAPositiveLaw {
                    reason: "outside the declared grid",
                },
            )
        };
        Ok((
            two_point(sources[index(&point[0], 3)?].clone()),
            two_point(receivers[index(&point[1], 3)?].clone()),
        ))
    }

    fn grid() -> ClockLift {
        ClockLift::new(vec![BigUint::from(3u32), BigUint::from(3u32)]).unwrap()
    }

    fn origin() -> Vec<BigInt> {
        vec![BigInt::from(0), BigInt::from(0)]
    }

    /// **The first law of learning.** Over every step the change of cross-entropy is exchange plus
    /// deposition, exactly as forms; along an aeon the sum is the boundary difference; over a cycle
    /// exchange is minus deposition. Lean `FirstLaw.first_law_epoch`, `first_law_aeon`,
    /// `cycle_exchange_eq_neg_deposition`.
    #[test]
    fn the_first_law_splits_the_change_of_cross_entropy() {
        let lift = grid();
        let aeon = lift
            .walk(
                origin(),
                &[(0, true), (1, true), (0, true), (1, true), (0, false)],
            )
            .unwrap();
        let cross = |point: &Vec<BigInt>| {
            let (p, q) = grid_laws(point).unwrap();
            p.cross_entropy(&q).unwrap()
        };
        for pair in aeon.occurrences().windows(2) {
            let ((p, q), (p_next, q_next)) =
                (grid_laws(&pair[0]).unwrap(), grid_laws(&pair[1]).unwrap());
            assert_eq!(
                cross(&pair[1]).minus(&cross(&pair[0])),
                exchange(&p, &p_next, &q)
                    .unwrap()
                    .plus(&deposition(&p_next, &q, &q_next).unwrap())
            );
        }
        let balance = learning_balance(&aeon, grid_laws).unwrap();
        assert_eq!(
            balance.total(),
            cross(aeon.end()).minus(&cross(aeon.start()))
        );
        let cycle = lift
            .walk(origin(), &[(0, true), (1, true), (0, false), (1, false)])
            .unwrap();
        let around = learning_balance(&cycle, grid_laws).unwrap();
        assert_eq!(around.exchange, around.deposition.scaled(&-Rat::one()));
    }

    /// [counterexample] **Exchange depends on the path.** From `(½, ½)` to `(¼, ⅓)`: moving the
    /// source first and then depositing exchanges `0`; depositing first exchanges `−¼` bit
    /// (`−(ln 2)/4` nats). The two aeons bound one square of the lift and change cross-entropy
    /// alike, so the exchange form is not closed while the total is. Lean
    /// `FirstLaw.PathWitness.exchange_is_path_dependent`.
    #[test]
    fn exchange_depends_on_the_path() {
        let lift = grid();
        let source_first = lift.walk(origin(), &[(0, true), (1, true)]).unwrap();
        let deposit_first = lift.walk(origin(), &[(1, true), (0, true)]).unwrap();
        let (a, b) = (
            learning_balance(&source_first, grid_laws).unwrap(),
            learning_balance(&deposit_first, grid_laws).unwrap(),
        );
        assert!(a.exchange.is_zero());
        assert_eq!(b.exchange, SymbolicSurprisal::term(2, rat(-1, 4)).unwrap());
        assert_eq!(a.total(), b.total());
    }
}
