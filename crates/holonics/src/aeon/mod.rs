//! **Aeon, epoch and cycle: the standard objects of time.**
//!
//! [definition] ([objects §12](../../../../docs/ELEMENTARY_OBJECTS.md#12-aeon-epoch-and-cycle-the-passage-of-time),
//! [record](../../../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)).
//! An **aeon** is the stretch of a Holarchy's motion between two occurrences: a chained word of
//! signed passages of its parametric complex, the 1-chain that keeps its order and so retains the
//! winding a bare endpoint pair forgets. The lift of the navigators' joint clock torus,
//! [`ClockLift`], is one such complex. An **epoch** is a division of an aeon at a receiver's
//! section, and a **cycle** is an aeon that returns to its phase state. No clock is privileged:
//! elapsed time is the pairing `t_R(γ) = ⟨ω_R | γ⟩ = n_R + r_R` of a receiver's clock (a closed
//! 1-form) with an aeon, read as whole windings (the quotient) and open phase (the remainder).
//!
//! Every value is exact. Where a law is logarithmic (production, cross-entropy), the operand is the
//! exact ratio product and the logarithm is carried as the exact ℚ-linear form in `log₂ p` of
//! [`crate::ratio::surprisal::SymbolicSurprisal`]; a numeric reading of it is its enclosure, an
//! exterior face.
//!
//! | Lean (library root `lean/Holonics/`) | Rust |
//! |---|---|
//! | `Aeon/Clock/Groupoid.ParametricComplex`, `Aeon`, `Aeon.concat`, `Aeon.reverse`, `Move.backtrack`, `Move.face`, `Move.faceReversed`, `instGroupoid` | [`ParametricComplex`], [`Aeon`], [`Aeon::concat`], [`Aeon::reverse`], [`Aeon::with_backtrack`], [`Aeon::with_cell`], [`Aeon::reduced`] |
//! | `Aeon/Clock/Reading.Clock`, `reading`, `reading_concat`, `reading_reverse`, `homotopy_invariant_iff_closed` | [`Clock`], [`ClosedForm`], [`Form`], [`reading`] |
//! | `Aeon/Clock/Reading.chainOf`, `cycle_reading_factors_through_homology` | [`FiniteComplex::chain`] |
//! | `Aeon/Clock/Reading.rate`, `Admitted`, `rate_swap`, `rate_through`, `rate_through_projectivelyEq`, `rate_through_zero`, `rate_iterate` | [`rate`], [`Aeon::repeated`] |
//! | `Aeon/Clock/Winding.clockLift`, `navigatorClock`, `torusPoint`, `torus_closes_iff` | [`ClockLift`], [`TorusClock`], [`Cycle`] |
//! | `Aeon/Clock/Winding.reading_navigatorClock`, `Aeon/Clock/Epoch.signed_count_is_flux` | [`ClockLift::forward`] (an aeon carried by its two lift points) |
//! | `Aeon/Clock/Winding.windings`, `openPhase`, `carry`, `windings_add`, `ratio_split`, `carry_of_microsteps`, `jump_iterate` | [`Reading`] |
//! | `Aeon/Clock/Lock.jointReading`, `IsCycle`, `lock_at_address`, `cycle_iff_period_dvd`, `convergent_near_return` | [`TwoClocks`], [`Convergent`], on the lift |
//! | `Aeon/Clock/Epoch.crossingTicks`, `aeonSection`, `epochOf`, `epoch`, `coarsen`, `epochOf_coarse`, `coarsen_tower`, `odometer_tower`, `CutClock`, `reading_eq_crossings`, `crossings_concat`, `sectionForm`, `signed_count_is_flux`, `ring_count_is_flux` | [`Epochs`], [`epochs`], [`EpochTower`], [`ClockLift::ring_section`] |
//! | `Aeon/Production/HodgeTime.TimeSplit`, `timeSplit_nonempty`, `timeSplit_unique`, `state_reading_of_walk`, `production_is_curvature`, `wordReading_eq_timeReading` | [`TimeSplit`], [`hodge_split`], read on aeons by [`Form::read`] |
//! | `Aeon/Production/PathReversal.pathLaw`, `production`, `epochProduction`, `pathLogRatio_split`, `detailedBalance_cycle_affinity_zero` | [`MarkovChain`], [`MarkovChain::production`], [`MarkovChain::heat`], [`MarkovChain::reversible_law`] |
//! | `Aeon/Production/Kac.FirstReturnEquations`, `firstReturn_existsUnique`, `kac_single_state`, `kac_grain_ratio` | [`MarkovChain::mean_return`], [`MarkovChain::grain_ratio`] |
//! | `Aeon/Production/Kac.epochEntropy`, `wordEntropy_succ`, `wordEntropy_eq_sum`, `abramov_ledger`, `abramov` | [`MarkovChain::epoch_entropy`], [`MarkovChain::word_entropy`], [`MarkovChain::abramov`] |
//! | `Physics/Information/ClockJoin.join_silent_on_cycles`, `join_of_silent_on_cycles`, `join_iff_silent`, `triangle_defect` | [`join_axes`], [`AxesJoin`], [`AxisComponent`], [`AxisRate`], [`ClockAxis`] |
//! | Mathlib `Matrix.charpolyRev`; `Aeon/Production/Zeta.cycleLog`, `zeta_eq_exp`, `machine_charpolyRev`, `machine_zeta` | [`ReturnMap`], [`zeta`], [`cycle_exponential`] |
//! | `Aeon/Production/FirstLaw.exchange`, `deposition`, `first_law_epoch`, `first_law_aeon` | [`PositiveLaw`], [`exchange`], [`deposition`], [`learning_balance`] |
//! | `Aeon/Production/FirstLaw.ledger_telescopes`, `ledger_is_first_law`, `enclosed_contains`, `enclosed_telescopes` | [`EnclosedLedger`], [`EnclosedBalance`], [`LiteralComparison`] |

use thiserror::Error;

use crate::holon::HolonError;
use crate::navigator::address::AddressError;
use crate::ratio::Rat;
use crate::ratio::linear::ExactLinearError;
use crate::ratio::surprisal::SurprisalError;

mod epoch;
mod first_law;
mod groupoid;
mod hodge;
mod join;
mod lock;
mod production;
mod reading;
mod zeta;

pub use epoch::{EpochTower, Epochs, Tick, epochs};
pub(crate) use first_law::weighted_surprisal;
pub use first_law::{
    EnclosedBalance, EnclosedLedger, LearningBalance, LiteralComparison, PositiveLaw, deposition,
    exchange, learning_balance,
};
pub use groupoid::{
    Aeon, ClockLift, Cycle, FiniteComplex, LiftPassage, LiftSquare, ParametricComplex, Step,
};
pub use hodge::{TimeSplit, hodge_split};
pub use join::{AxesJoin, AxisComponent, AxisRate, ClockAxis, join_axes};
pub use lock::{Convergent, TwoClocks};
pub use production::{MarkovChain, SectionEntropy, Transition};
pub use reading::{Clock, ClosedForm, Form, Reading, TorusClock, rate, reading};
pub use zeta::{ReturnMap, cycle_exponential, zeta};

/// Every refusal of the aeon objects. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum AeonError {
    #[error("step {position} is not a passage of the complex")]
    NotAPassage { position: usize },
    #[error("step {position} does not leave the occurrence the aeon has reached")]
    NotChained { position: usize },
    #[error("the first aeon does not end where the second begins")]
    NotComposable,
    #[error("the insertion point {position} lies outside the aeon")]
    PositionOutside { position: usize },
    #[error("the cell is not a two-cell of the complex")]
    NotACell,
    #[error("the cell's base is not the occurrence at insertion point {position}")]
    NotAtBase { position: usize },
    #[error("face {face}'s boundary word is not a closed chained loop at its base")]
    FaceNotALoop { face: usize },
    #[error("face {face}'s boundary word does not carry the complex's boundary column")]
    FaceNotItsBoundary { face: usize },
    #[error("the form reads {reading} around two-cell {cell}: it is not closed")]
    NotClosed { cell: usize, reading: Rat },
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("a circle of the clock torus needs a period of at least one micro-step")]
    ZeroPeriod,
    #[error("the aeon does not return to its phase state")]
    NotACycle,
    #[error("the cycle is repeated only a whole nonnegative number of times")]
    NotALoop,
    #[error("step {position} runs along a passage outside the clock's domain")]
    OutsideClock { position: usize },
    #[error(
        "neither receiver reads time along the aeon: the pair (0 : 0) is not an admitted ratio"
    )]
    Undetermined,
    #[error("grain {grain} ticks at {tick}, which the finer grain does not: not a sub-section")]
    NotASubsection { grain: usize, tick: usize },
    #[error("the grains read aeons of different lengths")]
    MicroStateMismatch,
    #[error("grain {grain} is not a grain of the tower")]
    GrainOutside { grain: usize },
    #[error("grain {fine} is coarser than grain {coarse}; coarsening runs fine to coarse")]
    NotFinerGrain { fine: usize, coarse: usize },
    #[error("the aeon's steps exceed the machine's address space")]
    BeyondAddressSpace,
    #[error("a clock ratio must be a positive rate")]
    NotAPositiveRate,
    #[error("row {state} is not a probability law: {reason}")]
    NotStochastic { state: usize, reason: &'static str },
    #[error("a law must be positive with total mass one: {reason}")]
    NotAPositiveLaw { reason: &'static str },
    #[error("the ledger has read no occurrence to step from")]
    NoOccurrence,
    #[error("navigator {navigator} ends behind where it starts: a forward aeon only advances")]
    NotForward { navigator: usize },
    #[error("the step {from} → {to} has no reverse transition, so the reversed aeon has no law")]
    IrreversibleStep { from: usize, to: usize },
    #[error(
        "the section of the first return is empty, outside the states, or carries no stationary mass"
    )]
    EmptySection,
    #[error("state {state} is named twice in the section: a section is a set of states")]
    RepeatedState { state: usize },
    #[error("the first-step equations have no solution: the chain is reducible off the section")]
    NoFirstReturn,
    #[error("the {what} is not unique: {free} free directions remain")]
    NotUnique { what: &'static str, free: usize },
    #[error("state {state} is not reached from state 0 through the support")]
    NotIrreducible { state: usize },
    #[error("the cycle {cycle:?} reads the ratio product {product}, not one: no detailed balance")]
    CycleObstruction { cycle: Vec<usize>, product: Rat },
    #[error("the split's harmonic remainder fails its certificate")]
    NotHarmonic,
    #[error("no rate is declared between any two clock axes")]
    NoDeclaredRate,
    #[error("the clock axis {axis:?} is not joined to the reference by any declared rate")]
    AxisNotJoined { axis: ClockAxis },
    #[error(
        "the clock axes do not join: the cycle {cycle:?} reads the holonomy {holonomy:?}, not one"
    )]
    AxesDefect {
        cycle: Vec<ClockAxis>,
        /// Boxed: the undivided pair of two exact rationals.
        holonomy: Box<crate::ratio::Presentation>,
    },
    #[error("the transfer determinant has no unit constant term")]
    NotAUnitSeries,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// Boxed: the Holon refusals carry exact inertia witnesses.
    #[error(transparent)]
    Holon(Box<HolonError>),
    #[error(transparent)]
    Address(#[from] AddressError),
    #[error(transparent)]
    Surprisal(#[from] SurprisalError),
}

impl From<HolonError> for AeonError {
    fn from(error: HolonError) -> Self {
        Self::Holon(Box::new(error))
    }
}
