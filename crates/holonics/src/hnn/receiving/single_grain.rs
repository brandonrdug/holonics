//! One grain read of log2(q_tree) + the rational receiving wave.
//!
//! The exact full value is represented by its cell and typed fibre identity. No rational
//! endpoint is used as the value. Only an unresolved cell refines its native logarithm.

use super::*;
use crate::ratio::algebraic::log2_enclosure_at;

/// Exact identity. Ord orders stored identities for distinction sets, not magnitudes;
/// consumers comparing widths must read certified enclosures instead.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ReceivingFibre {
    Rational(Rat),
    Logarithmic(LogarithmicFibre),
}

/// Exact constraint 2^(representative + epsilon) = probability * 2^wave.
/// Private fields bind this identity to its certified grain cell.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct LogarithmicFibre {
    probability: Rat,
    wave: Rat,
    representative: Rat,
    grain: u64,
}

impl LogarithmicFibre {
    pub fn probability(&self) -> &Rat {
        &self.probability
    }
    pub fn wave(&self) -> &Rat {
        &self.wave
    }
    pub fn representative(&self) -> &Rat {
        &self.representative
    }
    pub fn grain(&self) -> u64 {
        self.grain
    }
}

impl ReceivingFibre {
    pub fn as_rational(&self) -> Option<&Rat> {
        match self {
            Self::Rational(value) => Some(value),
            Self::Logarithmic(_) => None,
        }
    }

    /// Certified reading intersected with its admitted cell [0,1/grain).
    /// A closed upper endpoint of 1/grain encloses the strict bound; it is not a value.
    pub fn enclosure_at(&self, bits: u32) -> Result<ExactInterval, HnnError> {
        match self {
            Self::Rational(value) => Ok(ExactInterval::point(value.clone())),
            Self::Logarithmic(fibre) => {
                let log = log2_enclosure_at(&fibre.probability, bits)?;
                let lower = (log.lower + &fibre.wave - &fibre.representative).max(Rat::zero());
                let upper = (log.upper + &fibre.wave - &fibre.representative)
                    .min(Rat::new(BigInt::one(), BigInt::from(fibre.grain)));
                Ok(ExactInterval::new(lower, upper)?)
            }
        }
    }

    pub fn bits(&self) -> u64 {
        let size = |value: &Rat| value.numer().bits() + value.denom().bits();
        match self {
            Self::Rational(value) => size(value),
            Self::Logarithmic(fibre) => {
                size(&fibre.probability)
                    + size(&fibre.wave)
                    + size(&fibre.representative)
                    + (u64::BITS - fibre.grain.leading_zeros()) as u64
            }
        }
    }
}

/// A receiving class's exact grain cell. Generic rational GrainCell remains unchanged elsewhere.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingCell {
    pub carry: BigInt,
    pub phase: u64,
    pub fibre: ReceivingFibre,
}

impl From<GrainCell> for ReceivingCell {
    fn from(cell: GrainCell) -> Self {
        Self {
            carry: cell.carry,
            phase: cell.phase,
            fibre: ReceivingFibre::Rational(cell.fibre),
        }
    }
}

impl ReceivingCell {
    pub fn representative(&self, grain: u64) -> Rat {
        Rat::from_integer(self.carry.clone())
            + Rat::new(BigInt::from(self.phase), BigInt::from(grain))
    }

    pub fn rational_value(&self, grain: u64) -> Option<Rat> {
        self.fibre
            .as_rational()
            .map(|fibre| self.representative(grain) + fibre)
    }

    /// Full real logit, not merely its representative or the wave component.
    pub fn enclosure_at(&self, grain: u64, bits: u32) -> Result<ExactInterval, HnnError> {
        self.admit(grain)?;
        let fibre = self.fibre.enclosure_at(bits)?;
        let representative = self.representative(grain);
        Ok(ExactInterval::new(
            fibre.lower + &representative,
            fibre.upper + representative,
        )?)
    }

    pub(crate) fn admit(&self, grain: u64) -> Result<(), HnnError> {
        let invalid = || HnnError::Unadmitted {
            reason: "a receiving cell keeps its exact fibre identity in its declared grain",
        };
        if grain == 0 || self.phase >= grain {
            return Err(invalid());
        }
        match &self.fibre {
            ReceivingFibre::Rational(value) => {
                if value < &Rat::zero() || value >= &Rat::new(BigInt::one(), BigInt::from(grain)) {
                    return Err(invalid());
                }
            }
            ReceivingFibre::Logarithmic(fibre) => {
                if fibre.grain != grain || fibre.representative != self.representative(grain) {
                    return Err(invalid());
                }
            }
        }
        Ok(())
    }
}

fn read_cell(probability: &Rat, wave: &Rat, grain: u64) -> Result<ReceivingCell, HnnError> {
    let scale = Rat::from_integer(BigInt::from(grain));
    let mut bits = crate::ratio::exponentiated::READING_BITS;
    loop {
        // The native logarithm returns a point exactly on every power-of-two rational.
        // Otherwise log2(q) is irrational; adding a rational cannot land on a rational edge.
        // Refine only while the two certified endpoints name different cells.
        let log = log2_enclosure_at(probability, bits)?;
        let lower = ((&log.lower + wave) * &scale).floor().to_integer();
        let upper = ((&log.upper + wave) * &scale).floor().to_integer();
        if lower == upper {
            let representative = Rat::new(lower.clone(), BigInt::from(grain));
            let cell = GrainCell::of(&representative, grain);
            let fibre = if log.lower == log.upper {
                ReceivingFibre::Rational(log.lower + wave - &representative)
            } else {
                ReceivingFibre::Logarithmic(LogarithmicFibre {
                    probability: probability.clone(),
                    wave: wave.clone(),
                    representative,
                    grain,
                })
            };
            return Ok(ReceivingCell {
                carry: cell.carry,
                phase: cell.phase,
                fibre,
            });
        }
        // No fixed precision cap declares a wrong cell. Arithmetic inability to refine is fatal.
        bits = bits.checked_mul(2).ok_or(HnnError::CountOverflow)?;
    }
}

pub(super) fn combined(
    wave: Vec<Rat>,
    tree: &LandmarkFace,
    grain: u64,
) -> Result<ReceivingRead, HnnError> {
    let expected = tree
        .probabilities
        .len()
        .checked_mul(2)
        .ok_or(HnnError::CountOverflow)?;
    if expected != wave.len()
        || tree.exponents.len() != tree.probabilities.len()
        || tree.grain != grain
        || grain == 0
    {
        return Err(HnnError::Shape {
            what: "the tree face's grain logits against the wave's logits",
            expected: wave.len(),
            found: expected,
        });
    }
    let cells = (0..tree.probabilities.len())
        .map(|class| read_cell(&tree.probabilities[class], &wave[2 * class], grain))
        .collect::<Result<Vec<_>, _>>()?;
    let phases = wave.chunks(2).map(|pair| &pair[1] / integer(2)).collect();
    Ok(ReceivingRead {
        logits: wave,
        cells,
        phases,
    })
}

#[cfg(test)]
mod tests;
