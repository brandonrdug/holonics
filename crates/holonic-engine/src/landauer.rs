//! THE LANDAUER RATIO — what the cycle provably erased, against the budget the burn bought.
//!
//! # The hypothesis, and its owner
//!
//! Brandon's, folded into `blueprint/THE_EROS_INFORMATION_ENGINE.md` at his direction 2026-08-16:
//! *a real relationship between power input and purposed information compression*. Its formal owner
//! is the frozen laboratory —
//! `git -C /home/b/Workspaces/laboratory show a07ff376:src/eros/um/THEORY_AND_EQUATIONS.md` §18 —
//! which carries
//!
//! ```text
//!     Φ = P / (k·T·ln 2)   bits/s        bounded above by   Φ ≤ 2E/πℏ   (Margolus–Levitin)
//! ```
//!
//! graded `FORMAL`, and `…:src/docs/UNIVERSALITY_LIMIT.md` §2, which states the measurable as a
//! **Landauer efficiency**: the fraction of the thermodynamic budget converted into kept structure.
//!
//! Measured 2026-08-16 by `grep -rn "watt\|joule\|nvml\|power_draw" --include='*.rs' crates soma`:
//! **nothing in this tree computed it.** Landauer is carried in `canon/TABLET_THE_CAUSAL_PROFILE.md`
//! and nine research records, and computed nowhere. This module is that computation.
//!
//! # Three conditions, and none of them is a formality
//!
//! **1. Landauer bounds ERASURE, not transport.** Reversible computation has no such floor
//! (Bennett), so this law prices what a cycle **deletes** and never what it conducts. In this
//! corpus's own terms that is exact: it prices the **collapsing** generators and never the permuting
//! ones, and a rebase with zero remainder costs nothing here.
//!
//! **2. `T` is receiver-gauged.** Brandon, 2026-08-15: *"Temperature in physics is a statistic, it
//! has no place here… it is a gauged and relativistic holonic value."* So the budget is
//! receiver-relative and [`ThermalFrame`] carries the declaration rather than assuming one.
//!
//! **3. `P` has a clock in it.** The standing rule is that a cost is measured in work and that a
//! clock may measure but may never select. A power sample is therefore lawful **as a measurement
//! carrying its frame** — and the frame includes whether the device had an active display, which is
//! the second frame `the_carrier_is_admitted_by_its_work` established.
//!
//! # What is exact and what is not, stated rather than blurred
//!
//! The **numerator is exact and combinatorial**. Collapsing a population into blocks makes the map
//! from item to block many-to-one, and recovering the item from the block requires naming which
//! member — `⌈log₂ m⌉` bits for a block of extent `m`. Summed over blocks, that is the erasure, and
//! it is **zero exactly when every block is a singleton**, which is right: a partition that separates
//! everything deleted nothing. No distribution enters, and nothing is estimated.
//!
//! The **denominator is an enclosure**, because `ln 2` is irrational and this carrier is exact. It is
//! computed through `exact_analysis::log_rational_interval` at a caller-declared term count and
//! precision, so the budget is an interval and the comparison returns [`ExactOrdering`] with `Open`
//! where the interval straddles. **Nothing here divides into a float**, and the ratio is carried as
//! the undivided pair the horizon law admits.

use num_bigint::BigUint;
use num_traits::One;
use relational_geometry::exact_analysis::log_rational_interval;
use relational_geometry::{integer, Rat};

use crate::exact_value::ExactOrdering;

/// Why a reading refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LandauerError {
    /// A declared frame carried a non-positive temperature or interval. Refused rather than clamped:
    /// a zero interval buys no budget and a non-positive temperature is not a thermal frame.
    FrameIsNotPositive,
    /// The enclosure of `ln 2` could not be taken at the declared precision.
    LogarithmRefused,
}

/// The declared frame a power sample was taken in.
///
/// **Every field is an integer measurement carrying its own unit**, so nothing here is a float and
/// nothing is a ratio taken before its time. `display_active` is carried because a device under a
/// display load is a *second frame* rather than a contamination, and a measurement without its frame
/// is the absolute-frame defect.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThermalFrame {
    pub power_microwatts: u64,
    pub interval_nanoseconds: u64,
    /// The receiver's declared temperature. A gauged quantity, not a property of the material.
    pub temperature_millikelvin: u64,
    /// Whether the carrier had an active display while the sample was taken.
    pub display_active: bool,
    /// What the caller declares this sample is a frame *of*.
    pub declared_by: String,
}

/// What a collapse provably erased, and what the burn bought — carried as a pair, never divided.
#[derive(Clone, Debug)]
pub struct LandauerReading {
    /// `Σ over blocks of ⌈log₂ |block|⌉`. Exact, combinatorial, and zero on a separating partition.
    pub erased_bits: BigUint,
    /// The blocks that erased anything, with their extents. The members are the reading; a total
    /// alone could not say where the erasure happened.
    pub erasing_blocks: Vec<(usize, usize)>,
    /// `(P·Δt)/(k·T·ln 2)` as an enclosure, because `ln 2` is irrational and this carrier is exact.
    pub budget_lower: Rat,
    pub budget_upper: Rat,
    /// The frame the sample was taken in, carried so the reading cannot be quoted without it.
    pub frame: ThermalFrame,
}

impl LandauerReading {
    /// Where the erasure sits against the budget. `Open` when the enclosure straddles, which is an
    /// honest refusal rather than a rounded verdict.
    pub fn against_budget(&self) -> ExactOrdering {
        let erased = Rat::from(num_bigint::BigInt::from(self.erased_bits.clone()));
        if erased < self.budget_lower {
            ExactOrdering::Less
        } else if erased > self.budget_upper {
            ExactOrdering::Greater
        } else {
            ExactOrdering::Open
        }
    }

    /// The efficiency as the **undivided pair** `(erased, budget)`. A caller that wants a decimal
    /// takes one; this organ never forms it, because a ratio of a magnitude to a magnitude is what
    /// crosses a frame boundary and the quotient is not.
    pub fn efficiency_pair(&self) -> (BigUint, Rat, Rat) {
        (
            self.erased_bits.clone(),
            self.budget_lower.clone(),
            self.budget_upper.clone(),
        )
    }
}

/// `⌈log₂ n⌉` over integers — the bits needed to name one member of a population of `n`.
///
/// Exact and combinatorial: no logarithm is evaluated. `n ≤ 1` costs nothing, because naming the one
/// member of a singleton takes no bits, which is why a separating partition erases nothing.
#[must_use]
pub fn naming_bits(extent: usize) -> u64 {
    if extent <= 1 {
        return 0;
    }
    let mut bits = 0u64;
    let mut reach = 1usize;
    while reach < extent {
        reach = reach.saturating_mul(2);
        bits += 1;
    }
    bits
}

/// The erasure a partition performed, as bits and as the blocks that performed it.
///
/// The argument is the block extents, so this organ never learns what a block holds — it prices the
/// collapse and nothing else.
#[must_use]
pub fn erasure_of(block_extents: &[usize]) -> (BigUint, Vec<(usize, usize)>) {
    let mut bits = BigUint::ZERO;
    let mut erasing = Vec::new();
    for (at, extent) in block_extents.iter().enumerate() {
        let cost = naming_bits(*extent);
        if cost > 0 {
            bits += BigUint::from(cost);
            erasing.push((at, *extent));
        }
    }
    (bits, erasing)
}

/// Read a collapse against the budget a declared burn bought.
///
/// `k` enters as Boltzmann's constant in joules per kelvin. It is carried as an exact rational of the
/// SI defining value — `k = 1.380649 × 10⁻²³ J/K` exactly, since the 2019 redefinition fixed it — so
/// no physical constant is approximated here.
pub fn read(
    block_extents: &[usize],
    frame: ThermalFrame,
    logarithm_terms: u32,
    logarithm_bits: u32,
) -> Result<LandauerReading, LandauerError> {
    if frame.temperature_millikelvin == 0 || frame.interval_nanoseconds == 0 {
        return Err(LandauerError::FrameIsNotPositive);
    }
    let (erased_bits, erasing_blocks) = erasure_of(block_extents);

    // Energy in joules: microwatts × nanoseconds = 10^-6 W × 10^-9 s = 10^-15 J.
    let energy = Rat::new(
        num_bigint::BigInt::from(frame.power_microwatts) * num_bigint::BigInt::from(frame.interval_nanoseconds),
        num_bigint::BigInt::from(1_000_000_000_000_000u64),
    );
    // Boltzmann's constant, exact since the 2019 SI redefinition: 1.380649e-23 J/K.
    let boltzmann = Rat::new(
        num_bigint::BigInt::from(1_380_649u64),
        num_bigint::BigInt::from(10u64).pow(29),
    );
    let temperature = Rat::new(
        num_bigint::BigInt::from(frame.temperature_millikelvin),
        num_bigint::BigInt::from(1000u64),
    );
    let two = integer(2);
    let ln_two = log_rational_interval(&two, logarithm_terms, logarithm_bits)
        .map_err(|_| LandauerError::LogarithmRefused)?;

    // budget = energy / (k · T · ln2). Larger ln2 gives a SMALLER budget, so the enclosure inverts.
    let scale = boltzmann * temperature;
    if scale <= Rat::from(num_bigint::BigInt::from(0u32)) || ln_two.lower <= Rat::from(num_bigint::BigInt::from(0u32))
    {
        return Err(LandauerError::FrameIsNotPositive);
    }
    let budget_lower = energy.clone() / (scale.clone() * ln_two.upper.clone());
    let budget_upper = energy / (scale * ln_two.lower.clone());

    let _ = Rat::one();
    Ok(LandauerReading {
        erased_bits,
        erasing_blocks,
        budget_lower,
        budget_upper,
        frame,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame() -> ThermalFrame {
        ThermalFrame {
            power_microwatts: 250_000_000, // 250 W
            interval_nanoseconds: 1_000_000_000, // one second
            temperature_millikelvin: 300_000, // 300 K
            display_active: false,
            declared_by: "a declared control frame".to_owned(),
        }
    }

    /// **A separating partition erases nothing.** Every block a singleton, so naming a member costs
    /// no bits — which is the whole reason erasure and not transport is what this law prices.
    #[test]
    fn a_partition_into_singletons_erases_nothing() {
        let (bits, erasing) = erasure_of(&[1, 1, 1, 1, 1]);
        assert_eq!(bits, BigUint::ZERO);
        assert!(erasing.is_empty(), "no block erased, so none is named");
    }

    /// The bits are exact and combinatorial: a block of eight needs three bits to name a member.
    #[test]
    fn naming_a_member_costs_the_exact_ceiling() {
        assert_eq!(naming_bits(1), 0);
        assert_eq!(naming_bits(2), 1);
        assert_eq!(naming_bits(3), 2);
        assert_eq!(naming_bits(8), 3);
        assert_eq!(naming_bits(9), 4);
    }

    /// The blocks that erased are named, not counted — a total alone cannot say where.
    #[test]
    fn the_erasing_blocks_are_named_rather_than_totalled() {
        let (bits, erasing) = erasure_of(&[1, 4, 1, 8]);
        assert_eq!(bits, BigUint::from(5u32), "2 bits + 3 bits");
        assert_eq!(erasing, vec![(1, 4), (3, 8)]);
    }

    /// The budget is an ENCLOSURE and the comparison may return `Open`. A reading that always
    /// returned a verdict would have rounded the irrational away.
    #[test]
    fn the_budget_is_an_enclosure_and_the_comparison_can_be_open() {
        let reading = read(&[4, 4], frame(), 64, 128).expect("the frame reads");
        assert!(
            reading.budget_lower < reading.budget_upper,
            "ln 2 is irrational, so the budget is a proper interval"
        );
        // 250 J at 300 K buys on the order of 10^22 bits; four bits erased is far below it.
        assert_eq!(reading.against_budget(), ExactOrdering::Less);
        assert_eq!(reading.erased_bits, BigUint::from(4u32));
    }

    /// A frame that is not positive is refused rather than clamped.
    #[test]
    fn a_frame_that_is_not_positive_refuses() {
        let mut cold = frame();
        cold.temperature_millikelvin = 0;
        assert!(matches!(
            read(&[2], cold, 32, 64),
            Err(LandauerError::FrameIsNotPositive)
        ));
    }
}
