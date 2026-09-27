//! **The egg population: a receiver's Bayesian mixture over declared navigator families**
//! (`docs/ELEMENTARY_OBJECTS.md`, "The egg: a generator read as a whole";
//! `docs/RECEIVER_HOLARCHY.md`, "Probability is a receiver geometry"; rebuild step 4 item 4, #73).
//!
//! [definition; agent-inferred] **A population is a receiver's mixture over candidate eggs.** Each
//! candidate is a declared navigator family `f` ([`Family`]): its declared description `ℓ_f` bits,
//! its own predictive face `P_f(· | past)` on the declared cell alphabet, its deposit, and its
//! decoder's readout (its surviving keys, or its standing). No new object enters: the population
//! is the receiver's mixture and a family is a navigator family with its initial configuration
//! (the egg's genome) left to be located. The prior is Kraft's, `2^(−ℓ_f)`, normalized over the
//! declared families by their declared total mass `M = Σ_f 2^(−ℓ_f) ≤ 1` ([`Population::mass`];
//! the unused mass `1 − M` is declared beside it): `π_f = 2^(−ℓ_f)/M`.
//!
//! [proved-derived; formal-checked] **Selection is Bayes, and Bayes is the discrete replicator.**
//! A received cell `x` reweighs the families by their faces of it,
//! `w_f′ = w_f P_f(x)/Σ_g w_g P_g(x)` (Lean `Computation/HolonicAdjointNormalization.
//! {bayes_eq_face, bayes_eq_discrete_replicator}`), and the population's face is
//! `q(x) = Σ_f w_f P_f(x)` ([`Population::face`]). **A family dies exactly at zero likelihood**
//! (`replicator_eq_zero_iff`): a positive but poor face only lowers its weight; a family whose face
//! gives the received cell zero is released and never read again. The population's product of
//! faces telescopes to its families' likelihoods (Lean
//! `Compression/Landmark/Context/Population.population_mixture`, the static mixture with death):
//!
//! ```text
//! ∏_(t<n) q_t(x_t) = W = Σ_f π_f L_f,    L_f = ∏_(t<n) P_f(x_t | past)
//! −log₂ W ≤ −log₂ π_f − log₂ L_f          every family f alive at n
//! ```
//!
//! so the population's code ([`Population::code`]) is read once from its families' likelihoods and
//! never from carried weights: no chart drift enters it.
//!
//! [proved-derived; formal-checked] **A deterministic family is survivor filtering**
//! ([`Survivors`]; Lean `Population.survivor_code`). A finite key space `K` of emitters, each key
//! emitting one class a tick (the terrain's own navigators keyed by it), under the uniform prior:
//! the survivors `S_t` are the keys whose emissions agree with every cell before `t`; the family's
//! face of class `c` is the fraction of survivors emitting `c`, exact; and its likelihood
//! telescopes to `L = #S_n/|K|`, so its code is `log₂ |K| − log₂ #S_n`, the key description less
//! the surviving fibre (the key description itself when one key survives; the gauge orbit's
//! `log₂` less when a gauge fibre survives). A **factorized** key space `K = Π_i K_i` whose emission
//! is the mixed-radix tuple of the factors' emissions keeps a product of survivor sets, so its face
//! is the product of the factors' faces and its code the sum of theirs
//! (`Population.survivors_product`; [`KeyFamily`]).
//!
//! [definition; agent-inferred] **Why the population does not reuse the context tree's joins**
//! (`compression::landmark::context::{JoinTree, FaceJoins}`): the joins carry each two-face ratio
//! `β` on the tree's lattice and admit only digit faces inside the open unit interval. A
//! deterministic family's face is zero on the classes no survivor emits, and its death (zero
//! likelihood) is the replicator's law, which a positive carried ratio cannot reach. So the
//! population carries no weights at all: each family carries its own likelihood (exact for
//! survivors, `#S/|K|`; the tree's product of executed dyadic faces enclosed by
//! `compression::landmark::context::PassageCode`'s outward bounds), and the population's code, its
//! posteriors and its face are read from them through the telescope, each an exact enclosure
//! ([`Population::receipt`]). The bounds are kept at [`PRECISION`] significant bits, rounded
//! outward at every operation, and the codes are rounded out on the enclosure grid
//! (`ratio::algebraic::LOG_OCTAVES`).
//!
//! [definition; agent-inferred] **The owner.** The population is the receiver's: a receiver reads a
//! passage and weighs the navigator families it admits by their faces of it, so its owner is
//! `receiver::population`, beside `receiver::standing` (a standing is what one family retains; a
//! population is what the receiver retains over its families: each family's retained state and its
//! likelihood, never a record of the cells). The families it declares ([`families`]) read their
//! key spaces from the terrain's own declarations (`holarchy::terrain::MoireFamily`, the field's
//! ring for a rotor crib) and the receiving tree from `compression::landmark::context`.
//!
//! [open] **What the static population cannot do.** A family of fixed keys cannot follow an aeon
//! switch: on the dormant-grating terrain every grating key dies at the first cell the silent layer
//! changes, and the population falls to the tree (the notebook's receipt). Following it needs the
//! population's dormancy (campaign 3): a key held through the aeon in which its layer is silent
//! (its survivors kept with an activity reading per epoch, priced as a switch), which is the fixed
//! share across epochs (`hnn::receiving::Mixture::switching`, Lean
//! `Compression/Landmark/Context/LocalWeighing.fixed_share`) taken over a family's layers instead
//! of over two faces. The parity class's joint key space past the declared enumeration needs the
//! Bombe for a moiré ([`PopulationError::Bombe`]): parity-constraint propagation on the joint clock
//! torus, owed.
//!
//! [definition] The computational object is the helical pair interaction, read here as a
//! receiver's population of candidate eggs. Of the winding guide's six general objects this owner
//! touches three: the **helix** (a grating's key is its ring's rate and phase, a clock with carry,
//! read at its half-turn sheet; a rotor key's stage steps with the field's carry), **faces and
//! placement** (each family's face on the receiver's cell alphabet, and the population's face,
//! exact or enclosed) and the **tower thread** (the tree family's restrictions of the address). The
//! **pair** (a moiré's pairs lock, which a grating key names but no family reads), the **cell
//! holonomy** (none is claimed) and the **tube** (the passage, one cell a tick) stay attached.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Computation/HolonicAdjointNormalization.{bayes_eq_face, bayes_eq_discrete_replicator, replicator_eq_zero_iff}` | [`Population::receive`] (a family's weight moves by its face; zero face, death) |
//! | `Compression/Landmark/Context/LocalWeighing.static_mixture` (positive faces) | the telescope's positive case |
//! | `Compression/Landmark/Context/Population.population_mixture` (the static mixture with death) | [`Population::code`], [`Population::receipt`] |
//! | `Compression/Landmark/Context/Population.survivor_code` | [`Survivors`] |
//! | `Compression/Landmark/Context/Population.survivors_product` | [`KeyFamily`]'s factors |

pub mod families;

#[cfg(test)]
mod tests;

pub use families::{GratingParity, GratingSheet, RotorKeys, TreeFamily};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use rayon::prelude::*;
use thiserror::Error;

use crate::compression::landmark::context::{
    ContextError, Landmarks, PassageCode, ProductBound, ratio_code_length,
};
use crate::hnn::HnnError;
use crate::holarchy::terrain::TerrainError;
use crate::holon::contact::menu::MenuError;
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, ExactValueError, LOG_OCTAVES, interval_sum};

/// Every refusal of a population. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum PopulationError {
    #[error("{what}: {reason}")]
    Declaration {
        what: &'static str,
        reason: &'static str,
    },
    #[error("cell {cell} lies outside the declared alphabet of {alphabet}")]
    CellOutside { cell: usize, alphabet: usize },
    /// A key space past the declared enumeration: survivor filtering is refused, and its keys are
    /// owed to the named Bombe (the construction that locates them by loop closure).
    #[error(
        "the key space of {key_space} keys passes the declared enumeration of {admitted}: survivor filtering is refused; its keys are the Bombe's ({bombe})"
    )]
    Bombe {
        key_space: BigUint,
        admitted: BigUint,
        bombe: &'static str,
    },
    #[error(
        "every family's likelihood reached zero by cell {cell}: no declared family made the passage"
    )]
    Extinct { cell: usize },
    #[error(transparent)]
    Context(#[from] ContextError),
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    /// Boxed: a terrain's refusals are wide.
    #[error(transparent)]
    Terrain(Box<TerrainError>),
    /// Boxed: the HNN's refusals are wide.
    #[error(transparent)]
    Hnn(Box<HnnError>),
}

impl From<TerrainError> for PopulationError {
    fn from(error: TerrainError) -> Self {
        Self::Terrain(Box::new(error))
    }
}

impl From<HnnError> for PopulationError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

pub(crate) fn refuse(what: &'static str, reason: &'static str) -> PopulationError {
    PopulationError::Declaration { what, reason }
}

// -------------------------------------------------------------------------------------------
// the family

/// [definition] **A family's likelihood** `L_f = ∏_(t<n) P_f(x_t | past)`: exact (a survivor
/// family's `#S/|K|`), or enclosed by a passage's product bounds (the tree's executed dyadic faces,
/// `PassageCode`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Likelihood {
    Exact(Rat),
    Enclosed(PassageCode),
}

impl Likelihood {
    /// **The family's code alone** `−log₂ L_f`, enclosed; `None` at zero likelihood (a dead
    /// family's code is unbounded).
    pub fn code(&self) -> Result<Option<ExactInterval>, PopulationError> {
        match self {
            Likelihood::Exact(value) if value.is_zero() => Ok(None),
            Likelihood::Exact(value) => Ok(Some(ratio_code_length(
                value.numer().magnitude(),
                value.denom().magnitude(),
            )?)),
            Likelihood::Enclosed(passage) => Ok(Some(passage.bits()?)),
        }
    }

    /// Whether the likelihood is exactly zero.
    pub fn is_zero(&self) -> bool {
        matches!(self, Likelihood::Exact(value) if value.is_zero())
    }

    /// The likelihood's lower or upper bound.
    fn bound(&self, up: bool) -> Bound {
        match self {
            Likelihood::Exact(value) => Bound::of_rat(value, up),
            Likelihood::Enclosed(passage) => {
                let (numerator, denominator, exponent) = passage.bounds();
                let side = usize::from(up);
                // L ∈ [N_lower/(D_upper 2^E), N_upper/(D_lower 2^E)].
                let (n, d) = (numerator[side], denominator[1 - side]);
                Bound::of_product_bounds(n, d, exponent, up)
            }
        }
    }
}

/// [definition] **A key family's readout** (its decoder): each factor's key space `|K_i|` (one
/// factor for a joint key space) and each factor's surviving keys, each key its coordinates in the
/// family's declared layout ([`Emitters::coordinates`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyReadout {
    pub spaces: Vec<u64>,
    pub survivors: Vec<Vec<Vec<u64>>>,
}

impl KeyReadout {
    /// `|K| = Π_i |K_i|`.
    pub fn space(&self) -> BigUint {
        self.spaces.iter().map(|&s| BigUint::from(s)).product()
    }

    /// `#S = Π_i #S_i`.
    pub fn count(&self) -> BigUint {
        self.survivors
            .iter()
            .map(|keys| BigUint::from(keys.len()))
            .product()
    }
}

/// [definition] **A family's readout**: a key family's surviving keys, or a tree family's standing.
#[derive(Clone, Debug, PartialEq)]
pub enum Readout<'a> {
    Keys(KeyReadout),
    Standing(&'a Landmarks),
}

/// [definition] **A declared navigator family** (module header): a candidate egg read by the
/// receiver.
pub trait Family: Send {
    /// The family's declaration, for a receipt.
    fn label(&self) -> String;
    /// The declared cell alphabet.
    fn alphabet(&self) -> usize;
    /// `ℓ_f`: the declaration's description in bits (its prior is `2^(−ℓ_f)` before normalizing).
    fn description(&self) -> u64;
    /// `P_f(· | past)`: the family's face on the alphabet before the next cell, exact.
    fn face(&self) -> Result<Vec<Rat>, PopulationError>;
    /// **Receive one cell**: `P_f(x | past)` read before the deposit, then the deposit.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError>;
    /// `L_f`: the product of the faces received so far.
    fn likelihood(&self) -> Likelihood;
    /// The decoder's readout.
    fn readout(&self) -> Readout<'_>;
}

// -------------------------------------------------------------------------------------------
// the deterministic key family

/// [definition] **A declared finite key space of deterministic emitters** (module header, "A
/// deterministic family"): key `k < |K|` emits one class a tick; the emitters' navigators advance
/// together past each received cell.
pub trait Emitters: Send {
    /// The emitted classes' alphabet.
    fn alphabet(&self) -> usize;
    /// `|K|`.
    fn keys(&self) -> u64;
    /// The class key `k` emits at the current tick.
    fn emit(&self, key: u64) -> usize;
    /// Advance every key's navigator one tick past the received cell.
    fn advance(&mut self, cell: usize) -> Result<(), PopulationError>;
    /// Key `k`'s coordinates in the family's declared layout.
    fn coordinates(&self, key: u64) -> Vec<u64>;
}

/// [definition] **Survivor filtering** (module header): the uniform prior over a declared key
/// space, conditioned on the received cells. The survivors are held as key indices; before the
/// first cell every key survives and none is held.
pub struct Survivors {
    emitters: Box<dyn Emitters>,
    held: Option<Vec<u64>>,
    count: u64,
}

impl Survivors {
    /// **Declare survivor filtering** over the emitters' key space; refused at an empty key space,
    /// and past the declared enumeration `admitted`, naming the Bombe that owns the larger key
    /// space.
    pub fn new(
        emitters: Box<dyn Emitters>,
        admitted: u64,
        bombe: &'static str,
    ) -> Result<Self, PopulationError> {
        let keys = emitters.keys();
        if keys == 0 || emitters.alphabet() == 0 {
            return Err(refuse(
                "survivor filtering",
                "its key space and its alphabet each hold at least one member",
            ));
        }
        if keys > admitted {
            return Err(PopulationError::Bombe {
                key_space: BigUint::from(keys),
                admitted: BigUint::from(admitted),
                bombe,
            });
        }
        Ok(Self {
            emitters,
            held: None,
            count: keys,
        })
    }

    /// `#S`, the survivors.
    pub fn count(&self) -> u64 {
        self.count
    }

    /// `|K|`.
    pub fn keys(&self) -> u64 {
        self.emitters.keys()
    }

    /// The emitters.
    pub fn emitters(&self) -> &dyn Emitters {
        self.emitters.as_ref()
    }

    /// The surviving keys' indices, ascending.
    pub fn survivors(&self) -> Vec<u64> {
        match &self.held {
            Some(held) => held.clone(),
            None => (0..self.emitters.keys()).collect(),
        }
    }

    /// **Each class's surviving emitters** at the current tick.
    pub fn counts(&self) -> Vec<u64> {
        let mut counts = vec![0u64; self.emitters.alphabet()];
        let mut tally = |key: u64| {
            let class = self.emitters.emit(key);
            if let Some(count) = counts.get_mut(class) {
                *count += 1;
            }
        };
        match &self.held {
            Some(held) => held.iter().for_each(|&key| tally(key)),
            None => (0..self.emitters.keys()).for_each(tally),
        }
        counts
    }

    /// **The family's face**: each class's surviving emitters over the survivors, exact; all zero
    /// once no key survives.
    pub fn face(&self) -> Vec<Rat> {
        let total = BigInt::from(self.count);
        self.counts()
            .into_iter()
            .map(|count| {
                if self.count == 0 {
                    Rat::zero()
                } else {
                    Rat::new(BigInt::from(count), total.clone())
                }
            })
            .collect()
    }

    /// **Receive one cell**: the fraction of survivors emitting it, read before the deposit; then
    /// the survivors keep exactly the keys that emitted it, and every emitter advances.
    pub fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.emitters.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let before = self.count;
        let emitters = &self.emitters;
        let kept: Vec<u64> = match &self.held {
            Some(held) => held
                .iter()
                .copied()
                .filter(|&key| emitters.emit(key) == cell)
                .collect(),
            None => (0..emitters.keys())
                .filter(|&key| emitters.emit(key) == cell)
                .collect(),
        };
        self.count = kept.len() as u64;
        self.held = Some(kept);
        self.emitters.advance(cell)?;
        if before == 0 {
            return Ok(Rat::zero());
        }
        Ok(Rat::new(BigInt::from(self.count), BigInt::from(before)))
    }

    /// `#S/|K|`, exact.
    pub fn likelihood(&self) -> Rat {
        Rat::new(BigInt::from(self.count), BigInt::from(self.emitters.keys()))
    }
}

/// [definition] **A key family** (module header): survivor filtering over a key space of one
/// factor, or over a factorized one whose cell is the mixed-radix tuple of its factors' classes
/// (the first factor least significant).
pub struct KeyFamily {
    label: String,
    description: u64,
    factors: Vec<Survivors>,
}

impl KeyFamily {
    /// The family of the declared factors; refused without a factor.
    pub fn new(
        label: String,
        description: u64,
        factors: Vec<Survivors>,
    ) -> Result<Self, PopulationError> {
        if factors.is_empty() {
            return Err(refuse("a key family", "it holds at least one factor"));
        }
        Ok(Self {
            label,
            description,
            factors,
        })
    }

    /// The factors.
    pub fn factors(&self) -> &[Survivors] {
        &self.factors
    }

    /// Each factor's digit of a cell.
    fn digits(&self, mut cell: usize) -> Vec<usize> {
        self.factors
            .iter()
            .map(|factor| {
                let radix = factor.emitters.alphabet();
                let digit = cell % radix;
                cell /= radix;
                digit
            })
            .collect()
    }
}

impl Family for KeyFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.factors
            .iter()
            .map(|factor| factor.emitters.alphabet())
            .product()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let faces: Vec<Vec<Rat>> = self.factors.iter().map(Survivors::face).collect();
        Ok((0..self.alphabet())
            .map(|cell| {
                self.digits(cell)
                    .iter()
                    .zip(&faces)
                    .map(|(&digit, face)| face[digit].clone())
                    .product()
            })
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let digits = self.digits(cell);
        let mut face = Rat::one();
        for (factor, digit) in self.factors.iter_mut().zip(digits) {
            face *= factor.receive(digit)?;
        }
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.factors.iter().map(Survivors::likelihood).product())
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: self.factors.iter().map(Survivors::keys).collect(),
            survivors: self
                .factors
                .iter()
                .map(|factor| {
                    factor
                        .survivors()
                        .into_iter()
                        .map(|key| factor.emitters.coordinates(key))
                        .collect()
                })
                .collect(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the population

/// [definition; agent-inferred] **The kept precision** `P = 2·O` significant bits (`O` the enclosure
/// grid's octaves, `ratio::algebraic::LOG_OCTAVES`): a bound kept at `P` bits moves by a relative
/// `2^(1−P)` at most, so its `log₂` by less than `3·2^(−P)` (`log₂ e < 3/2`), and a reading of at most
/// `2^(O − 2)` kept operations stays within `2^(−O)` of the exact one, the grid the codes are
/// rounded out on.
pub const PRECISION: u64 = 2 * LOG_OCTAVES as u64;

/// A nonnegative bound `m · 2^e`, its mantissa kept at [`PRECISION`] significant bits, rounded
/// down (a lower bound) or up (an upper bound) at every operation.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Bound {
    mantissa: BigUint,
    exponent: i64,
}

impl Bound {
    fn zero() -> Self {
        Self {
            mantissa: BigUint::zero(),
            exponent: 0,
        }
    }

    fn is_zero(&self) -> bool {
        self.mantissa.is_zero()
    }

    /// `m 2^e` kept at `P` bits, rounded up when `up` and a dropped bit is set.
    fn kept(mantissa: BigUint, exponent: i64, up: bool) -> Self {
        let bits = mantissa.bits();
        if bits <= PRECISION {
            return Self { mantissa, exponent };
        }
        let shift = bits - PRECISION;
        let dropped = mantissa.trailing_zeros().is_some_and(|zeros| zeros < shift);
        let mut kept = &mantissa >> shift as usize;
        if up && dropped {
            kept += 1u32;
        }
        Self {
            mantissa: kept,
            exponent: exponent + shift as i64,
        }
    }

    /// `n/d` kept at `P` bits (`d > 0`).
    fn of_ratio(numerator: &BigUint, denominator: &BigUint, up: bool) -> Self {
        if numerator.is_zero() {
            return Self::zero();
        }
        let shift = (PRECISION + 1 + denominator.bits()).saturating_sub(numerator.bits());
        let scaled = numerator << shift as usize;
        let (quotient, remainder) = (&scaled / denominator, &scaled % denominator);
        let quotient = if up && !remainder.is_zero() {
            quotient + 1u32
        } else {
            quotient
        };
        Self::kept(quotient, -(shift as i64), up)
    }

    /// A nonnegative rational kept at `P` bits.
    fn of_rat(value: &Rat, up: bool) -> Self {
        Self::of_ratio(value.numer().magnitude(), value.denom().magnitude(), up)
    }

    /// `N/(D 2^E)` from a passage's product bounds.
    fn of_product_bounds(
        numerator: ProductBound,
        denominator: ProductBound,
        exponent: u64,
        up: bool,
    ) -> Self {
        let mut bound = Self::of_ratio(
            &BigUint::from(numerator.mantissa),
            &BigUint::from(denominator.mantissa),
            up,
        );
        bound.exponent += numerator.exponent as i64 - denominator.exponent as i64 - exponent as i64;
        bound
    }

    fn times(&self, other: &Bound, up: bool) -> Self {
        Self::kept(
            &self.mantissa * &other.mantissa,
            self.exponent + other.exponent,
            up,
        )
    }

    fn plus(&self, other: &Bound, up: bool) -> Self {
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        let exponent = self.exponent.min(other.exponent);
        let align = |b: &Bound| &b.mantissa << (b.exponent - exponent) as usize;
        Self::kept(align(self) + align(other), exponent, up)
    }

    /// `self/other` (`other > 0`).
    fn over(&self, other: &Bound, up: bool) -> Self {
        let mut bound = Self::of_ratio(&self.mantissa, &other.mantissa, up);
        if !bound.is_zero() {
            bound.exponent += self.exponent - other.exponent;
        }
        bound
    }

    /// `−log₂(m 2^e)`, enclosed (`m > 0`).
    fn code(&self) -> Result<ExactInterval, PopulationError> {
        let log = ratio_code_length(&self.mantissa, &BigUint::one())?;
        let shift = Rat::from_integer(BigInt::from(self.exponent));
        Ok(ExactInterval {
            lower: &log.lower - &shift,
            upper: &log.upper - &shift,
        })
    }

    /// The bound as an exact rational, on the grid `2^(−P)` (rounded down, or up when `up`).
    fn to_rat(&self, up: bool) -> Rat {
        let grid = -(PRECISION as i64);
        if self.exponent >= grid {
            let value = BigInt::from(self.mantissa.clone());
            return if self.exponent >= 0 {
                Rat::from_integer(value << self.exponent as usize)
            } else {
                Rat::new(value, BigInt::one() << (-self.exponent) as usize)
            };
        }
        let shift = (grid - self.exponent) as usize;
        let mut floor = &self.mantissa >> shift;
        if up
            && self
                .mantissa
                .trailing_zeros()
                .is_some_and(|zeros| (zeros as usize) < shift)
        {
            floor += 1u32;
        }
        Rat::new(BigInt::from(floor), BigInt::one() << PRECISION as usize)
    }
}

/// `[lower, upper]` of `−log₂ x` from `x`'s bounds `[x_lower, x_upper]` (`x_lower > 0`), rounded
/// out on the enclosure grid.
fn code_between(lower: &Bound, upper: &Bound) -> Result<ExactInterval, PopulationError> {
    let enclosure = ExactInterval::new(upper.code()?.lower, lower.code()?.upper)?;
    Ok(interval_sum(
        &ExactInterval::point(Rat::zero()),
        &enclosure,
    )?)
}

/// [definition] **A family's posterior**: exactly zero (the family died at zero likelihood), or
/// `−log₂ w_f` enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Posterior {
    Dead,
    Bits(ExactInterval),
}

/// [definition] **One family's receipt** ([`Population::receipt`]): its declaration and description
/// `ℓ_f`, its normalized prior `π_f`, the cell it died at (zero likelihood), its code alone
/// `−log₂ L_f` and charged `−log₂(π_f L_f)` (none once dead), its posterior, and its keys' readout.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyReceipt {
    pub label: String,
    pub description: u64,
    pub prior: Rat,
    pub died: Option<usize>,
    pub code: Option<ExactInterval>,
    pub charged: Option<ExactInterval>,
    pub posterior: Posterior,
    pub keys: Option<KeyReadout>,
}

/// [definition] **The population's receipt**: the cells received, the declared total mass `M`, the
/// population's code `−log₂ W` (exact enclosure), each family's receipt, and the family the
/// population selects: the one whose posterior is decided above one half (`−log₂ w_f < 1`), if any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PopulationReceipt {
    pub cells: usize,
    pub mass: Rat,
    pub code: ExactInterval,
    pub families: Vec<FamilyReceipt>,
    pub selected: Option<usize>,
}

struct Member {
    family: Box<dyn Family>,
    prior: Rat,
    died: Option<usize>,
}

/// [definition; agent-inferred] **The population** (module header): the declared families with
/// their normalized Kraft prior, each carrying its own likelihood.
pub struct Population {
    members: Vec<Member>,
    alphabet: usize,
    mass: Rat,
    cells: usize,
}

impl Population {
    /// **Declare the population** over its families: one alphabet, and descriptions whose Kraft sum
    /// `M = Σ_f 2^(−ℓ_f)` is at most one (a prefix code's lengths); the prior is `2^(−ℓ_f)/M`.
    pub fn new(families: Vec<Box<dyn Family>>) -> Result<Self, PopulationError> {
        let Some(first) = families.first() else {
            return Err(refuse("a population", "it declares at least one family"));
        };
        let alphabet = first.alphabet();
        if alphabet == 0 || families.iter().any(|family| family.alphabet() != alphabet) {
            return Err(refuse(
                "a population",
                "its families read one declared cell alphabet",
            ));
        }
        let kraft = |family: &dyn Family| -> Result<Rat, PopulationError> {
            let bits = usize::try_from(family.description())
                .map_err(|_| refuse("a family's description", "it fits the address space"))?;
            Ok(Rat::new(BigInt::one(), BigInt::one() << bits))
        };
        let weights = families
            .iter()
            .map(|family| kraft(family.as_ref()))
            .collect::<Result<Vec<Rat>, _>>()?;
        let mass: Rat = weights.iter().sum();
        if mass > Rat::one() {
            return Err(refuse(
                "a population's descriptions",
                "their Kraft sum passes one: they are no prefix code's lengths",
            ));
        }
        let members = families
            .into_iter()
            .zip(weights)
            .map(|(family, weight)| Member {
                family,
                prior: weight / &mass,
                died: None,
            })
            .collect();
        Ok(Self {
            members,
            alphabet,
            mass,
            cells: 0,
        })
    }

    /// The declared cell alphabet.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// **The declared total mass** `M = Σ_f 2^(−ℓ_f)`; the unused mass is `1 − M`.
    pub fn mass(&self) -> &Rat {
        &self.mass
    }

    /// The cells received.
    pub fn cells(&self) -> usize {
        self.cells
    }

    /// The families, in their declared order.
    pub fn families(&self) -> impl Iterator<Item = &dyn Family> {
        self.members.iter().map(|member| member.family.as_ref())
    }

    /// Family `f`'s normalized prior `π_f`.
    pub fn prior(&self, family: usize) -> Option<&Rat> {
        self.members.get(family).map(|member| &member.prior)
    }

    /// The cell family `f` died at, if it died.
    pub fn died(&self, family: usize) -> Option<usize> {
        self.members.get(family).and_then(|member| member.died)
    }

    /// One member's reception of one cell: its face of the cell read and deposited; at zero, death.
    fn member_receives(
        member: &mut Member,
        position: usize,
        cell: usize,
    ) -> Result<(), PopulationError> {
        if member.died.is_some() {
            return Ok(());
        }
        let face = member.family.receive(cell)?;
        if face.is_zero() {
            member.died = Some(position);
        } else if !face.is_positive() || face > Rat::one() {
            return Err(refuse(
                "a family's face of a cell",
                "it lies in the unit interval",
            ));
        }
        Ok(())
    }

    fn check(&self, cell: usize) -> Result<(), PopulationError> {
        if cell >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        Ok(())
    }

    fn extinct(&self) -> Option<usize> {
        if self.members.iter().all(|member| member.died.is_some()) {
            self.members.iter().filter_map(|member| member.died).max()
        } else {
            None
        }
    }

    /// **Receive one cell** (module header): every living family's face of it is read and
    /// deposited; a family whose face gives it zero dies. Refused when every family is dead.
    pub fn receive(&mut self, cell: usize) -> Result<(), PopulationError> {
        self.check(cell)?;
        let position = self.cells;
        for member in &mut self.members {
            Self::member_receives(member, position, cell)?;
        }
        self.cells += 1;
        match self.extinct() {
            Some(cell) => Err(PopulationError::Extinct { cell }),
            None => Ok(()),
        }
    }

    /// **Receive a passage** (the host realization of [`Population::receive`] over its cells): the
    /// families run together on the host's cores, each reading the shared immutable cells in order
    /// and writing only its own state, so their effects commute (the hardware law) and each family's
    /// state, likelihood and death are those of the cell-by-cell reception.
    pub fn receive_passage(&mut self, cells: &[usize]) -> Result<(), PopulationError> {
        for &cell in cells {
            self.check(cell)?;
        }
        let start = self.cells;
        self.members.par_iter_mut().try_for_each(|member| {
            for (offset, &cell) in cells.iter().enumerate() {
                Self::member_receives(member, start + offset, cell)?;
                if member.died.is_some() {
                    break;
                }
            }
            Ok::<_, PopulationError>(())
        })?;
        self.cells += cells.len();
        match self.extinct() {
            Some(cell) => Err(PopulationError::Extinct { cell }),
            None => Ok(()),
        }
    }

    /// Each member's `π_f L_f` bounds `(lower, upper)`; zero once dead.
    fn charged_bounds(&self) -> Vec<(Bound, Bound)> {
        self.members
            .iter()
            .map(|member| {
                if member.died.is_some() {
                    return (Bound::zero(), Bound::zero());
                }
                let likelihood = member.family.likelihood();
                let (prior_lower, prior_upper) = (
                    Bound::of_rat(&member.prior, false),
                    Bound::of_rat(&member.prior, true),
                );
                (
                    prior_lower.times(&likelihood.bound(false), false),
                    prior_upper.times(&likelihood.bound(true), true),
                )
            })
            .collect()
    }

    /// `W`'s bounds over the declared members.
    fn total(bounds: &[(Bound, Bound)], members: impl Iterator<Item = usize>) -> (Bound, Bound) {
        members.fold((Bound::zero(), Bound::zero()), |(lower, upper), f| {
            (
                lower.plus(&bounds[f].0, false),
                upper.plus(&bounds[f].1, true),
            )
        })
    }

    /// **The population's code** `−log₂ W = −log₂ Σ_f π_f L_f`, an exact enclosure (module header:
    /// the telescope). Refused when every family is dead.
    pub fn code(&self) -> Result<ExactInterval, PopulationError> {
        let bounds = self.charged_bounds();
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        code_between(&lower, &upper)
    }

    /// **The posterior of a set of families** `−log₂ Σ_(f ∈ set) w_f`, enclosed; `Dead` when every
    /// family of the set is dead.
    pub fn posterior_of(&self, set: &[usize]) -> Result<Posterior, PopulationError> {
        if set.iter().any(|&f| f >= self.members.len()) {
            return Err(refuse("a set of families", "it names declared families"));
        }
        let bounds = self.charged_bounds();
        let (part_lower, part_upper) = Self::total(&bounds, set.iter().copied());
        if part_upper.is_zero() {
            return Ok(Posterior::Dead);
        }
        // Every family outside the set is dead: the set's posterior is exactly one.
        if (0..self.members.len()).all(|f| set.contains(&f) || self.members[f].died.is_some()) {
            return Ok(Posterior::Bits(ExactInterval::point(Rat::zero())));
        }
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        if part_lower.is_zero() {
            return Err(refuse(
                "a posterior's enclosure",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        // −log₂ w ∈ [code(part_upper) − code(W_lower), code(part_lower) − code(W_upper)].
        let (part, whole) = (
            ExactInterval::new(part_upper.code()?.lower, part_lower.code()?.upper)?,
            ExactInterval::new(upper.code()?.lower, lower.code()?.upper)?,
        );
        // A posterior is at most one: its code is never negative.
        let enclosure = ExactInterval::new(
            (&part.lower - &whole.upper).max(Rat::zero()),
            (&part.upper - &whole.lower).max(Rat::zero()),
        )?;
        Ok(Posterior::Bits(interval_sum(
            &ExactInterval::point(Rat::zero()),
            &enclosure,
        )?))
    }

    /// **The population's face** `q(c) = Σ_f w_f P_f(c)` before the next cell, each class enclosed
    /// on the grid `2^(−P)` (the weights' bounds are read from the likelihoods: module header).
    pub fn face(&self) -> Result<Vec<ExactInterval>, PopulationError> {
        let bounds = self.charged_bounds();
        let (lower, upper) = Self::total(&bounds, 0..bounds.len());
        if lower.is_zero() {
            return Err(PopulationError::Extinct { cell: self.cells });
        }
        let mut sums = vec![(Bound::zero(), Bound::zero()); self.alphabet];
        for (member, (charged_lower, charged_upper)) in self.members.iter().zip(&bounds) {
            if member.died.is_some() {
                continue;
            }
            let (weight_lower, weight_upper) = (
                charged_lower.over(&upper, false),
                charged_upper.over(&lower, true),
            );
            for (sum, face) in sums.iter_mut().zip(member.family.face()?) {
                let (face_lower, face_upper) =
                    (Bound::of_rat(&face, false), Bound::of_rat(&face, true));
                sum.0 = sum.0.plus(&weight_lower.times(&face_lower, false), false);
                sum.1 = sum.1.plus(&weight_upper.times(&face_upper, true), true);
            }
        }
        sums.into_iter()
            .map(|(lower, upper)| {
                let upper = upper.to_rat(true).min(Rat::one());
                Ok(ExactInterval::new(lower.to_rat(false), upper)?)
            })
            .collect()
    }

    /// **The population's receipt** (module header).
    pub fn receipt(&self) -> Result<PopulationReceipt, PopulationError> {
        let code = self.code()?;
        let bounds = self.charged_bounds();
        let mut families = Vec::with_capacity(self.members.len());
        let mut selected = None;
        for (index, (member, (lower, upper))) in self.members.iter().zip(&bounds).enumerate() {
            let alive = member.died.is_none();
            let posterior = self.posterior_of(&[index])?;
            if let Posterior::Bits(bits) = &posterior
                && bits.upper < Rat::one()
            {
                selected = Some(index);
            }
            families.push(FamilyReceipt {
                label: member.family.label(),
                description: member.family.description(),
                prior: member.prior.clone(),
                died: member.died,
                code: if alive {
                    member.family.likelihood().code()?
                } else {
                    None
                },
                charged: if alive && !lower.is_zero() {
                    Some(code_between(lower, upper)?)
                } else {
                    None
                },
                posterior,
                keys: match member.family.readout() {
                    Readout::Keys(keys) => Some(keys),
                    Readout::Standing(_) => None,
                },
            });
        }
        Ok(PopulationReceipt {
            cells: self.cells,
            mass: self.mass.clone(),
            code,
            families,
            selected,
        })
    }

    /// Family `f`'s readout.
    pub fn readout(&self, family: usize) -> Option<Readout<'_>> {
        self.members
            .get(family)
            .map(|member| member.family.readout())
    }
}
