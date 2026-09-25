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
//!
//! [definition] **The ledger read on enclosed code lengths** ([`EnclosedLedger`], Lean
//! `FirstLaw.{ledger_telescopes, ledger_is_first_law, enclosed_contains, enclosed_telescopes}`).
//! A receiver whose faces lie in an algebraic extension (the HNN's `ℚ(θ)`, `θ^L = 2`) reads its code
//! length `C(s, Θ) = −Σ log₂ p̂_Θ(t)` of the arrived targets `s` at the constitution `Θ` only as an
//! exact enclosure: the logarithm of an algebraic normalizer is not a form in `log₂ p` of
//! rationals. The occurrences of the learning aeon are the pairs `(s, Θ)`, and each step moves one
//! coordinate:
//!
//! ```text
//! exchange     C(s_k, Θ_k) − C(s_(k−1), Θ_k)        new targets arrive through the unchanged constitution
//! deposition   C(s_k, Θ_(k+1)) − C(s_k, Θ_k)        the constitution moves at the arrived targets
//! ```
//!
//! The exact values telescope to `C(closing) − C(opening)` over any walk of such steps
//! (`ledger_telescopes`); where `C` is a cross-entropy of positive laws the two sums are
//! `first_law_aeon`'s (`ledger_is_first_law`). Read on enclosures `[lo_k, hi_k] ∋ C_k`, each step is
//! the exact Minkowski difference `[lo_(k+1) − hi_k, hi_(k+1) − lo_k]`, each sum contains its exact
//! value (`enclosed_contains`), and the two sums together are the enclosed change widened by the
//! widths of the interior occurrences, exactly (`enclosed_telescopes`):
//! `total.lower = (lo_N − hi_0) − W`, `total.upper = (hi_N − lo_0) + W`, `W = Σ_(0<k<N) (hi_k − lo_k)`.
//! Nothing is rounded: the enclosures' own endpoints are added and subtracted exactly.
//!
//! [definition] **The face against the literal** ([`LiteralComparison`]; the perceived-difference
//! record, §2). Per arrived cell `log₂|A| = ℓ_k + g_k` with `ℓ_k = −log₂ p̂_k(t_k)` and
//! `g_k = log₂(|A| p̂_k(t_k))`, so over an aeon's arrivals `Σ ℓ_k + Σ g_k = n·log₂|A|`. It is exact
//! algebra and a reading, not a budget: `g_k < 0` wherever the face predicts worse than uniform.

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ParametricComplex};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::surprisal::SymbolicSurprisal;
use num_traits::{One, Signed, Zero};

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

// ---------------------------------------------------------------------------------------------
// The ledger read on enclosed code lengths
// ---------------------------------------------------------------------------------------------

/// `a + b` of two enclosures: the exact Minkowski sum.
fn plus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower + &b.lower,
        upper: &a.upper + &b.upper,
    }
}

/// `a − b` of two enclosures: the exact Minkowski difference.
fn minus(a: &ExactInterval, b: &ExactInterval) -> ExactInterval {
    ExactInterval {
        lower: &a.lower - &b.upper,
        upper: &a.upper - &b.lower,
    }
}

fn width(a: &ExactInterval) -> Rat {
    &a.upper - &a.lower
}

fn zero() -> ExactInterval {
    ExactInterval::point(Rat::zero())
}

/// [definition] **One aeon's first law read on enclosed code lengths** (module header): the
/// summed exchange and deposition steps, the code lengths at the aeon's opening and closing
/// occurrences, the widening `W` (the widths of its interior occurrences), and the arrivals: the
/// summed code length `Σ ℓ_k(Θ_k)` of every arrival read at the constitution it arrived through,
/// with their cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnclosedBalance {
    pub exchange: ExactInterval,
    pub deposition: ExactInterval,
    /// The code length at the occurrence the aeon opened at; `None` before any reading.
    pub opening: Option<ExactInterval>,
    /// The code length at the occurrence the aeon has reached; `None` before any reading.
    pub closing: Option<ExactInterval>,
    /// `W = Σ (hi_k − lo_k)` over the aeon's interior occurrences.
    pub widening: Rat,
    /// The steps taken: exchanges (arrivals after the first reading, and releases) and depositions.
    pub exchanges: u64,
    pub depositions: u64,
    /// The arrivals read in the aeon (the first reading of all included), their cells and summed
    /// code length.
    pub arrivals: u64,
    pub cells: u64,
    pub arrived: ExactInterval,
}

impl EnclosedBalance {
    fn opened(at: Option<ExactInterval>) -> Self {
        Self {
            exchange: zero(),
            deposition: zero(),
            opening: at.clone(),
            closing: at,
            widening: Rat::zero(),
            exchanges: 0,
            depositions: 0,
            arrivals: 0,
            cells: 0,
            arrived: zero(),
        }
    }

    /// `exchange + deposition`: the enclosed sum of every step.
    pub fn total(&self) -> ExactInterval {
        plus(&self.exchange, &self.deposition)
    }

    /// **The aeon's change of code length**, `C(closing) − C(opening)` enclosed; zero, exactly,
    /// when the aeon took no step. The total is this change widened by the widening on each side,
    /// exactly (Lean `enclosed_telescopes`).
    pub fn change(&self) -> ExactInterval {
        match (&self.opening, &self.closing) {
            (Some(opening), Some(closing)) if self.exchanges + self.depositions > 0 => {
                minus(closing, opening)
            }
            _ => zero(),
        }
    }

    /// **The face against a literal of `per_cell` bits per cell** over the aeon's arrivals.
    pub fn against_literal(&self, per_cell: &ExactInterval) -> LiteralComparison {
        let cells = Rat::from_integer(self.cells.into());
        let literal = ExactInterval {
            lower: &per_cell.lower * &cells,
            upper: &per_cell.upper * &cells,
        };
        LiteralComparison {
            cells: self.cells,
            gain: minus(&literal, &self.arrived),
            code: self.arrived.clone(),
            literal,
        }
    }
}

/// [definition] **The face against the literal over an aeon** (module header): `n` cells, the
/// face's code `Σ ℓ_k`, the literal `n·log₂|A|` and the gain `Σ g_k = n·log₂|A| − Σ ℓ_k`, each
/// enclosed. `code + gain = literal` holds for the exact values; the gain is the exact reflection
/// of the code's enclosure when the literal is a point (`|A|` a power of two). A reading, not a
/// budget: the gain is negative wherever the face predicts worse than uniform.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LiteralComparison {
    pub cells: u64,
    pub code: ExactInterval,
    pub literal: ExactInterval,
    pub gain: ExactInterval,
}

/// [definition] **The running ledger of the first law on enclosed code lengths** (module header):
/// the balance of the aeon in progress, whose closing is the occurrence the ledger has reached.
/// The first reading opens it; every later reading is a step from the occurrence reached, so the
/// steps chain and telescope. At an aeon boundary [`EnclosedLedger::close`] returns the aeon's
/// balance and opens the next aeon at the occurrence reached: aeons concatenate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnclosedLedger {
    aeon: EnclosedBalance,
}

impl Default for EnclosedLedger {
    fn default() -> Self {
        Self::new()
    }
}

impl EnclosedLedger {
    /// A ledger that has read no occurrence.
    pub fn new() -> Self {
        Self {
            aeon: EnclosedBalance::opened(None),
        }
    }

    /// The balance of the aeon in progress.
    pub fn balance(&self) -> &EnclosedBalance {
        &self.aeon
    }

    /// One step from the occurrence reached to `next`, into exchange or deposition.
    fn step(&mut self, next: ExactInterval, deposition: bool) -> Result<(), AeonError> {
        let at = self.aeon.closing.take().ok_or(AeonError::NoOccurrence)?;
        let moved = minus(&next, &at);
        if self.aeon.exchanges + self.aeon.depositions > 0 {
            self.aeon.widening += width(&at);
        }
        if deposition {
            self.aeon.deposition = plus(&self.aeon.deposition, &moved);
            self.aeon.depositions += 1;
        } else {
            self.aeon.exchange = plus(&self.aeon.exchange, &moved);
            self.aeon.exchanges += 1;
        }
        self.aeon.closing = Some(next);
        Ok(())
    }

    /// **New targets arrive** through the unchanged constitution, read at `code` over `cells`
    /// cells: an exchange step from the occurrence reached, or the ledger's opening when it has
    /// read none.
    pub fn arrive(&mut self, code: ExactInterval, cells: u64) {
        self.aeon.arrived = plus(&self.aeon.arrived, &code);
        self.aeon.arrivals += 1;
        self.aeon.cells += cells;
        if self.aeon.closing.is_some() {
            self.step(code, false).expect("an occurrence has been read");
        } else {
            self.aeon.opening = Some(code.clone());
            self.aeon.closing = Some(code);
        }
    }

    /// **The constitution moved at the arrived targets**, which now read `reread`: a deposition
    /// step. Refused before any reading.
    pub fn deposit(&mut self, reread: ExactInterval) -> Result<(), AeonError> {
        self.step(reread, true)
    }

    /// **The constitution moved by a release** (the collapse at an aeon boundary), the arrived
    /// targets now reading `reread`: the released part, counted as exchange. Refused before any
    /// reading.
    pub fn release(&mut self, reread: ExactInterval) -> Result<(), AeonError> {
        self.step(reread, false)
    }

    /// **Close the aeon**: its balance, and the next aeon opened at the occurrence reached.
    pub fn close(&mut self) -> EnclosedBalance {
        let reached = self.aeon.closing.clone();
        std::mem::replace(&mut self.aeon, EnclosedBalance::opened(reached))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aeon::groupoid::ClockLift;
    use crate::ratio::{integer, rat};
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

    fn enclosed(value: Rat, below: Rat, above: Rat) -> ExactInterval {
        ExactInterval::new(&value - below, value + above).unwrap()
    }

    /// **The enclosed ledger telescopes.** Rational code lengths `C(s, Θ)` on a grid, each read as
    /// an enclosure of its own width, along a walk that arrives, deposits and releases: each sum
    /// contains its exact value, the exact values telescope to `C(closing) − C(opening)`, and the
    /// enclosed total is the enclosed change widened by the interior widths on each side, exactly;
    /// closing the aeon opens the next at the occurrence reached, and the two aeons' changes add.
    /// Lean `FirstLaw.{ledger_telescopes, enclosed_contains, enclosed_telescopes}`.
    #[test]
    fn the_enclosed_ledger_telescopes() {
        // C(s, Θ) = (s + 1)/(Θ + 2) + s·Θ/3: any exact table.
        let code = |s: i64, theta: i64| rat(s + 1, theta + 2) + rat(s * theta, 3);
        let widths = [
            rat(1, 8),
            rat(0, 1),
            rat(3, 16),
            rat(1, 4),
            rat(1, 2),
            rat(1, 32),
        ];
        // (kind, s, Θ) after each reading: 0 arrive, 1 deposit, 2 release.
        let walk = [
            (0, 0, 0),
            (1, 0, 1),
            (0, 1, 1),
            (0, 2, 1),
            (1, 2, 2),
            (2, 2, 3),
        ];
        let mut ledger = EnclosedLedger::new();
        assert_eq!(ledger.deposit(zero()), Err(AeonError::NoOccurrence));
        let (mut exchange, mut deposition) = (Rat::zero(), Rat::zero());
        let mut previous: Option<Rat> = None;
        for (index, &(kind, s, theta)) in walk.iter().enumerate() {
            let exact = code(s, theta);
            let read = enclosed(
                exact.clone(),
                widths[index].clone(),
                widths[5 - index].clone(),
            );
            match kind {
                0 => ledger.arrive(read, 2),
                1 => ledger.deposit(read).unwrap(),
                _ => ledger.release(read).unwrap(),
            }
            if let Some(before) = previous {
                if kind == 1 {
                    deposition += &exact - before;
                } else {
                    exchange += &exact - before;
                }
            }
            previous = Some(exact);
        }
        let aeon = ledger.close();
        assert_eq!(
            (aeon.exchanges, aeon.depositions, aeon.arrivals, aeon.cells),
            (3, 2, 3, 6)
        );
        let inside = |interval: &ExactInterval, value: &Rat| {
            interval.lower <= *value && *value <= interval.upper
        };
        assert!(inside(&aeon.exchange, &exchange) && inside(&aeon.deposition, &deposition));
        assert_eq!(&exchange + &deposition, code(2, 3) - code(0, 0));
        let (total, change) = (aeon.total(), aeon.change());
        assert!(inside(&change, &(code(2, 3) - code(0, 0))));
        let interior: Rat = (1..5).map(|k| &widths[k] + &widths[5 - k]).sum();
        assert_eq!(aeon.widening, interior);
        assert_eq!(total.lower, &change.lower - &aeon.widening);
        assert_eq!(total.upper, &change.upper + &aeon.widening);
        // The next aeon opens where this one closed; aeons concatenate.
        assert_eq!(ledger.balance().opening, aeon.closing);
        assert_eq!(ledger.balance().change(), zero());
        ledger.arrive(ExactInterval::point(code(3, 3)), 2);
        let next = ledger.close();
        assert_eq!(
            next.change(),
            minus(
                &ExactInterval::point(code(3, 3)),
                aeon.closing.as_ref().unwrap()
            )
        );
    }

    /// **The enclosed ledger reads the first law of `learning_balance`.** Along the same aeon of
    /// the grid, the source's steps arriving and the receiver's depositing, each cross-entropy
    /// read as its enclosure: the ledger's exchange and deposition meet the enclosures of the exact
    /// forms `learning_balance` sums. Lean `FirstLaw.ledger_is_first_law`.
    #[test]
    fn the_enclosed_ledger_reads_the_learning_balance() {
        let lift = grid();
        let moves = [(0, true), (1, true), (0, true), (1, true)];
        let aeon = lift.walk(origin(), &moves).unwrap();
        let cross = |point: &Vec<BigInt>| {
            let (p, q) = grid_laws(point).unwrap();
            p.cross_entropy(&q).unwrap().enclosure().unwrap()
        };
        let mut ledger = EnclosedLedger::new();
        ledger.arrive(cross(aeon.start()), 1);
        for ((navigator, _), occurrence) in moves.iter().zip(aeon.occurrences().iter().skip(1)) {
            if *navigator == 0 {
                ledger.arrive(cross(occurrence), 1);
            } else {
                ledger.deposit(cross(occurrence)).unwrap();
            }
        }
        let exact = learning_balance(&aeon, grid_laws).unwrap();
        let read = ledger.close();
        let meets = |a: &ExactInterval, b: &ExactInterval| a.lower <= b.upper && b.lower <= a.upper;
        assert!(meets(&read.exchange, &exact.exchange.enclosure().unwrap()));
        assert!(meets(
            &read.deposition,
            &exact.deposition.enclosure().unwrap()
        ));
        assert!(meets(&read.change(), &exact.total().enclosure().unwrap()));
    }

    /// **The face against the literal.** `Σ ℓ + Σ g = n·log₂|A|`: with `|A| = 4` (two bits a cell)
    /// the gain is the exact reflection of the code's enclosure, and a face that predicts worse than
    /// uniform (`p̂ = 1/16`, four bits) gains `−2` bits: a reading, not a budget.
    #[test]
    fn the_face_against_the_literal_is_exact_algebra() {
        let mut ledger = EnclosedLedger::new();
        ledger.arrive(ExactInterval::point(integer(4)), 1);
        let worse = ledger
            .balance()
            .against_literal(&ExactInterval::point(integer(2)));
        assert_eq!(worse.gain, ExactInterval::point(integer(-2)));
        ledger.arrive(enclosed(rat(1, 2), rat(1, 64), rat(1, 32)), 1);
        let read = ledger
            .close()
            .against_literal(&ExactInterval::point(integer(2)));
        assert_eq!(read.cells, 2);
        assert_eq!(read.literal, ExactInterval::point(integer(4)));
        assert_eq!(read.gain.lower, &read.literal.lower - &read.code.upper);
        assert_eq!(read.gain.upper, &read.literal.upper - &read.code.lower);
    }
}
