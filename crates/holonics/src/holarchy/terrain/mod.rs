//! **Terrain a declared Holarchy made: learning is gauged where the truth is exact** (the record
//! `2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_…_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md`, §3.3
//! and §5; rebuild step 4, #73).
//!
//! [definition; agent-inferred, the record's §3.3] **Learning is prototyped on terrain a Holarchy
//! made.** A declared Holarchy, run over declared aeons with drawn keys and constitution, emits the
//! cells; its truth is exact and returned beside them, so a learner is gauged three ways:
//! **redundancy** (its code minus the true rate's code, never only against baselines),
//! **recovery** (the located keys and constitution against the drawn ones) and **attribution**
//! (each terrain holds one kind of structure). The keys are drawn by a seeded exact draw
//! ([`Draw`]), never posed, and the terrain is made of the objects the machine is made of. The
//! conversation cut stays the living substrate and the milestone (Brandon's ruling of August 26):
//! a terrain's receipt is a development receipt, never mixed with the cut's in one claim.
//!
//! | Terrain | Its Holarchy | Its truth receipt | The mechanism it isolates |
//! |---|---|---|---|
//! | [`Moire`] | `k` closing rotor rings (the HNN's own ring, `navigator::Navigator::rotor`), no contacts: gratings whose overlap is read only at the receiver's face; its parametric orientation the rings' joint clock torus ([`Moire::parametric`], as `Holarchy::parametric` builds it) | [`MoireTruth`]: the rates and phases (the keys), the joint period `lcm(q_i)` (the torus's cycle), the emission's least period and determining depth, each pair's lock address, the entropy rate zero, and the key description `⌈log₂ |key space|⌉` | the rings: lock, resonance |
//! | [`TreeSource`] | a shift-closed pruned context tree whose leaves hold drawn faces: the shift navigator with its standing, the leaf map (Lean `Compression/Landmark/Context/Standing.leaf_standing`) | [`TreeSourceTruth`]: the tree and faces, the leaf chain's stationary law solved over ℚ, the entropy rate as its exact form in `log₂ p` and its enclosure; per passage the source's own code ([`TreeSource::passage`]), the weighting bound ([`TreeSource::weighting_bound`]) and the recovered tree ([`TreeSource::recovery`]) | the receiving tree: does it recover the tree and reach the rate? |
//! | [`RotorCrib`] | a declared HNN field's ring as a reflector machine behind a plugboard | [`CribTruth`]: the key and the plugboard, and their description | key location |
//! | [`Switching`] | two sources alternating by drawn aeons; for [`Switching::dormant`] one moiré whose grating is silent in the odd aeons while its ring keeps turning | [`SwitchTruth`]: the switch epochs as `aeon::Epochs` of the cell clock's forward aeon at the switch section, and the dormant grating | dormancy across aeon boundaries (campaign 3) |
//!
//! [definition; agent-inferred] **The draw is a navigator** ([`Draw`]): a Weyl rotation of
//! `ℤ/2^64` by the odd step `γ = ⌊2^64/φ⌋ = 0x9E37_79B9_7F4A_7C15`, whose orbit is the whole circle
//! (a cycle of `2^64` ticks), keyed by its seed and read through the bijective SplitMix64 mix face
//! (Steele, Lea and Flood 2014, [proved-standard]). A draw below `b` rejects the `2^64 mod b` least
//! words, so it is exactly uniform on `ℤ/b` given uniform words, and a family's key description
//! `⌈log₂ |key space|⌉` is the cost of naming a drawn key. It is the crate's one seeded draw: the
//! tests read it too (`hnn::tests::support`, `compression::landmark::context::tests`,
//! `compression::keys::edges`).
//!
//! [open] **The founding (sieve) variant of the moiré** (the record's §5: gratings founded at the
//! gaps, the laboratory's prime-stream microscope, commit `3450a0bc`, `found.rs::comb_upto`) is not
//! built. It would need a founding law on the Holarchy: a grating whose period is the least
//! uncovered residue of the gratings already laid (the cokernel: faces no current ring reaches),
//! joined by `Holon::interconnect` at that tick, so the terrain's Holarchy grows along its own
//! aeon; its truth would be the founding ticks (the primes) and the coverage (the composites'
//! least factors), and its chance threshold the moiré null `μ` of independent gratings.
//!
//! [definition] The computational object is the helical pair interaction, here as the terrain it
//! meets. Of the winding guide's six general objects this owner touches three: the **helix** (a
//! grating is a ring turning `p/q` of a turn a tick, circle plus carry, read at grain 2 as its
//! half-turn sheet; the draw is a Weyl rotation), **faces and placement** (the receiver's grain:
//! the sheet, the parity color, a leaf's face on its grid) and the **tube** (the aeon's span, one
//! cell a tick; the switch epochs divide it). The **pair** (each two gratings' lock address), the
//! **cell holonomy** (none is claimed: the gratings exchange no power) and the **tower thread**
//! (the context tree restricts an address to its leaf) stay attached.

pub mod crib;
pub mod moire;
pub mod source;
pub mod switching;

#[cfg(test)]
mod tests;

pub use crib::{CribTruth, RotorCrib, rotor_crib};
pub use moire::{Grating, Moire, MoireClass, MoireFamily, MoireTruth, PairLock};
pub use source::{
    ContextTree, Passage, Recovery, TreeSource, TreeSourceFamily, TreeSourceTruth, WeightingBound,
};
pub use switching::{AeonFamily, SwitchTruth, Switching};

use thiserror::Error;

use crate::aeon::AeonError;
use crate::compression::landmark::context::ContextError;
use crate::hnn::HnnError;
use crate::holon::HolonError;
use crate::holon::contact::menu::MenuError;
use crate::navigator::address::AddressError;
use crate::ratio::algebraic::ExactValueError;
use crate::ratio::linear::ExactLinearError;
use crate::ratio::surprisal::SurprisalError;

/// Every refusal of a terrain. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum TerrainError {
    #[error("{what}: {reason}")]
    Declaration {
        what: &'static str,
        reason: &'static str,
    },
    /// Boxed: the HNN's refusals are wide.
    #[error(transparent)]
    Hnn(Box<HnnError>),
    /// Boxed: the aeon's refusals are wide.
    #[error(transparent)]
    Aeon(Box<AeonError>),
    #[error(transparent)]
    Context(#[from] ContextError),
    #[error(transparent)]
    Holon(#[from] HolonError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    /// Boxed: an address refusal carries its operands.
    #[error(transparent)]
    Address(Box<AddressError>),
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Surprisal(#[from] SurprisalError),
}

impl From<HnnError> for TerrainError {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

impl From<AeonError> for TerrainError {
    fn from(error: AeonError) -> Self {
        Self::Aeon(Box::new(error))
    }
}

impl From<AddressError> for TerrainError {
    fn from(error: AddressError) -> Self {
        Self::Address(Box::new(error))
    }
}

fn refuse(what: &'static str, reason: &'static str) -> TerrainError {
    TerrainError::Declaration { what, reason }
}

/// [definition; agent-inferred] **The seeded exact draw** (module header): the Weyl rotation of
/// `ℤ/2^64` by `γ = ⌊2^64/φ⌋`, keyed by the seed, read through the SplitMix64 mix face. Its words
/// are exact integers; nothing here is a float.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Draw(u64);

impl Draw {
    /// The rotation's step `γ = ⌊2^64/φ⌋`, odd, so the rotation's orbit is all of `ℤ/2^64`.
    pub const STEP: u64 = 0x9E37_79B9_7F4A_7C15;

    /// The draw keyed by `seed`: the rotation's initial configuration.
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// **The next word**: one tick of the rotation, read through the bijective mix face. A word,
    /// never an iterator's option: the rotation has no end.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(Self::STEP);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// **A draw below `bound`**, exactly uniform on `ℤ/bound` given uniform words: a word among the
    /// `2^64 mod bound` least is rejected and the rotation ticks again, so the accepted words are
    /// whole turns of `ℤ/bound`. `bound ≥ 1`; a bound of zero names no value and is refused by a
    /// panic, a caller's defect.
    pub fn below(&mut self, bound: usize) -> usize {
        let bound = u64::try_from(bound).expect("a bound within a machine word");
        assert!(bound > 0, "a draw below zero names no value");
        let rejected = bound.wrapping_neg() % bound;
        loop {
            let word = self.next();
            if word >= rejected {
                return usize::try_from(word % bound).expect("a value below a usize bound");
            }
        }
    }

    /// **A fair coin**: the word's least bit, exactly one half each side.
    pub fn coin(&mut self) -> bool {
        self.next() & 1 == 1
    }
}
