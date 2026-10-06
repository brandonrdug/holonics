//! **Phase, winding and carry; the face around a cell.**
//!
//! The helix is the circle with its carry retained ([winding guide](../../../../docs/WINDING_CARRY_AND_PLACEMENT.md)).
//! This module is the exact owner of phase, winding and carry on a circle of `n` steps, the
//! mixed-radix odometer that cascades them, the integer winding of a closed loop, and the holonomy
//! of affine transports around a triangular cell. Every value is an exact integer or rational.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Geometry/PhaseCarry.phase_add_winding` | [`phase`], [`winding`] |
//! | `Geometry/PhaseCarry.winding_add`, `carry_le_one`, `carry_cocycle` | [`carry`] |
//! | `Geometry/PhaseCarry.digits_succ`, `odometer_iterate`, `value_digits` | [`Odometer`] |
//! | `Geometry/PhaseCarry.closed_loop_has_integer_winding` | [`closed_loop_winding`] |
//! | `Transport/CellHolonomy.triangleHolonomy`, `regauge`, `triangleHolonomy_regauge` | [`triangle_holonomy`], [`regauge`] |
//! | `Transport/CellHolonomy.holonomy_trace_is_gauge_free` | [`linear_trace`] |

use crate::geometry::{AffineMap3, RatMat3, RatVec3};
use crate::ratio::Rat;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use thiserror::Error;

/// Every refusal this module can return. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum WindingError {
    #[error("a circle of zero steps carries no phase chart")]
    ZeroModulus,
    #[error("odometer level {level} declares radix {radix}; a level needs at least two states")]
    DegenerateRadix { level: usize, radix: BigUint },
    #[error("odometer level {level} holds digit {digit}, which does not lie below radix {radix}")]
    DigitOutOfRange {
        level: usize,
        digit: BigUint,
        radix: BigUint,
    },
    #[error("an odometer declared {radices} radices and {digits} digits")]
    LevelCountMismatch { radices: usize, digits: usize },
    #[error(
        "the lifted loop does not close on the circle of {modulus} steps; remainder {remainder}"
    )]
    LoopDoesNotClose { modulus: BigInt, remainder: BigInt },
    #[error("a gauge frame must be invertible")]
    SingularGauge,
    #[error("the holonomy carries curvature, so its translation part is not a Burgers step")]
    CurvedHolonomy,
}

// ---------------------------------------------------------------------------------------------
// 1. Phase, winding and carry
// ---------------------------------------------------------------------------------------------

/// [definition] The phase of `x` on the circle of `n` steps. Lean: `PhaseCarry.phase`.
pub fn phase(n: &BigUint, x: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(x % n)
}

/// [definition] The winding of `x`: completed turns of the circle of `n` steps.
/// Lean: `PhaseCarry.winding`, with `phase_add_winding` giving `phase + n*winding = x`.
pub fn winding(n: &BigUint, x: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(x / n)
}

/// [definition] The carry of two phases: the turn completed by adding them.
///
/// [proved-derived; implemented-exact] It is the exact defect of the winding's additivity
/// (`PhaseCarry.winding_add`), never exceeds one turn (`carry_le_one`) and is a cocycle
/// (`carry_cocycle`). The tests exercise all three.
pub fn carry(n: &BigUint, a: &BigUint, b: &BigUint) -> Result<BigUint, WindingError> {
    if n.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    Ok(((a % n) + (b % n)) / n)
}

/// [proved-derived; implemented-exact] A closed loop of lifted integer increments has an integer
/// winding. Lean: `PhaseCarry.closed_loop_has_integer_winding`. A loop that does not close is
/// refused carrying its exact remainder rather than rounded to the nearest turn.
///
/// Cost: one pass over the increments.
pub fn closed_loop_winding(
    modulus: &BigInt,
    increments: &[BigInt],
) -> Result<BigInt, WindingError> {
    if modulus.is_zero() {
        return Err(WindingError::ZeroModulus);
    }
    let total: BigInt = increments.iter().sum();
    let remainder = &total % modulus;
    if !remainder.is_zero() {
        return Err(WindingError::LoopDoesNotClose {
            modulus: modulus.clone(),
            remainder,
        });
    }
    Ok(total / modulus)
}

/// [definition] A mixed-radix odometer: the cascade in which each level advances by the winding of
/// the level below. Lean: `PhaseCarry.odometer`, `digits`, `value`.
///
/// `overflow_winding` is the completed turns of the whole cascade — the material a product of
/// independent circles would have dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Odometer {
    radices: Vec<BigUint>,
    digits: Vec<BigUint>,
    overflow_winding: BigUint,
}

impl Odometer {
    /// A validated odometer at rest. Each radix must admit at least two states: a one-state level
    /// holds no phase, so its digit chart would read nothing and every step would be a carry.
    pub fn new(radices: Vec<BigUint>) -> Result<Self, WindingError> {
        let digits = vec![BigUint::zero(); radices.len()];
        Self::with_digits(radices, digits)
    }

    /// A validated odometer at a declared reading: one digit per level, each strictly below its
    /// radix.
    pub(crate) fn with_digits(
        radices: Vec<BigUint>,
        digits: Vec<BigUint>,
    ) -> Result<Self, WindingError> {
        if radices.len() != digits.len() {
            return Err(WindingError::LevelCountMismatch {
                radices: radices.len(),
                digits: digits.len(),
            });
        }
        let two = BigUint::from(2u32);
        for (level, radix) in radices.iter().enumerate() {
            if *radix < two {
                return Err(WindingError::DegenerateRadix {
                    level,
                    radix: radix.clone(),
                });
            }
            if digits[level] >= *radix {
                return Err(WindingError::DigitOutOfRange {
                    level,
                    digit: digits[level].clone(),
                    radix: radix.clone(),
                });
            }
        }
        Ok(Self {
            radices,
            digits,
            overflow_winding: BigUint::zero(),
        })
    }

    /// Read a value into the digit chart. Lean: `PhaseCarry.digits` iterated up the cascade.
    pub fn from_value(radices: Vec<BigUint>, value: &BigUint) -> Result<Self, WindingError> {
        let mut odometer = Self::new(radices)?;
        let mut remaining = value.clone();
        for level in 0..odometer.radices.len() {
            odometer.digits[level] = &remaining % &odometer.radices[level];
            remaining /= &odometer.radices[level];
        }
        odometer.overflow_winding = remaining;
        Ok(odometer)
    }

    pub fn radices(&self) -> &[BigUint] {
        &self.radices
    }

    pub fn digits(&self) -> &[BigUint] {
        &self.digits
    }

    pub fn overflow_winding(&self) -> &BigUint {
        &self.overflow_winding
    }

    pub fn levels(&self) -> usize {
        self.radices.len()
    }

    /// One act-and-advance step. Lean: `PhaseCarry.digits_succ`.
    pub fn step(&mut self) {
        self.advance(&BigUint::one());
    }

    /// Advance by `k` at once. Lean: `PhaseCarry.odometer_iterate` — the level above advances by
    /// the winding of the level below, so `k` is never counted down.
    ///
    /// Cost: at most one big-integer division and remainder per level, independent of `k`'s
    /// magnitude; it is linear in the number of levels and in `k`'s digit length, not in `k`.
    pub fn advance(&mut self, k: &BigUint) {
        let mut incoming = k.clone();
        for level in 0..self.radices.len() {
            if incoming.is_zero() {
                break;
            }
            let total = &self.digits[level] + &incoming;
            self.digits[level] = &total % &self.radices[level];
            incoming = total / &self.radices[level];
        }
        self.overflow_winding += incoming;
    }

    /// The value the digit chart carries. Lean: `PhaseCarry.value_digits` — the chart is faithful.
    ///
    /// Cost: one Horner pass down the levels.
    pub fn value(&self) -> BigUint {
        let mut total = self.overflow_winding.clone();
        for level in (0..self.radices.len()).rev() {
            total = total * &self.radices[level] + &self.digits[level];
        }
        total
    }
}

// ---------------------------------------------------------------------------------------------
// 4. Cell holonomy: the face around a cell is a screw
// ---------------------------------------------------------------------------------------------

/// [definition] The holonomy of three affine transports around a triangular cell, based at vertex
/// `0`: apply `g01`, then `g12`, then `g20`. Lean: `CellHolonomy.triangleHolonomy`, whose group
/// product `g01 * g12 * g20` is this left-to-right application order.
///
/// Its linear part is the cell's curvature and, when that part is the identity, its translation is
/// the Burgers step ([`burgers_step`]).
pub fn triangle_holonomy(g01: &AffineMap3, g12: &AffineMap3, g20: &AffineMap3) -> AffineMap3 {
    g01.followed_by(g12).followed_by(g20)
}

/// [definition] Regauging an edge transport by the vertex frames `ki`, `kj`:
/// `kᵢ⁻¹ ∘ g ∘ kⱼ` in the same order. Lean: `CellHolonomy.regauge`. A singular frame is refused.
pub fn regauge(
    ki: &AffineMap3,
    kj: &AffineMap3,
    g: &AffineMap3,
) -> Result<AffineMap3, WindingError> {
    let inverse = ki.inverse().ok_or(WindingError::SingularGauge)?;
    Ok(inverse.followed_by(g).followed_by(kj))
}

/// [definition] The trace of an affine map's linear part: a gauge-free face of the holonomy.
/// Lean: `CellHolonomy.holonomy_trace_is_gauge_free`.
pub fn linear_trace(map: &AffineMap3) -> Rat {
    &map.linear.rows[0][0] + &map.linear.rows[1][1] + &map.linear.rows[2][2]
}

/// [definition] The Burgers step of a cell: the translation part of a holonomy whose linear part is
/// the identity. A holonomy that rotates carries curvature, and its translation is then frame
/// dependent, so it is refused rather than reported.
pub fn burgers_step(holonomy: &AffineMap3) -> Result<&RatVec3, WindingError> {
    if holonomy.linear != RatMat3::identity() {
        return Err(WindingError::CurvedHolonomy);
    }
    Ok(&holonomy.translation)
}

#[cfg(test)]
mod tests;
