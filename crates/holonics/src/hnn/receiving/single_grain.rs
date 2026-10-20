//! One grain read of log2(q_tree) + the rational receiving wave.
//!
//! The exact full value is represented by its cell and typed fibre identity. No rational
//! endpoint is used as the value. Only an unresolved cell refines its native logarithm.

use super::*;
use crate::ratio::algebraic::log2_enclosure_at;
use num_traits::Signed;

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

/// Reads the exact probability mass carried by each retained receiving cell.  The declaration
/// authenticates the cells' source grain; it does not rebin them.  In particular, a logarithmic
/// fibre contributes its exact native tree probability times the rational wave power, while a
/// rational fibre contributes its exact full rational logit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RetainedFibreReceiver {
    source_grain: u64,
}

impl RetainedFibreReceiver {
    pub fn declare(source_grain: u64) -> Result<Self, HnnError> {
        if source_grain == 0 {
            return Err(HnnError::Unadmitted {
                reason: "a retained-fibre receiver needs a nonzero source grain",
            });
        }
        Ok(Self { source_grain })
    }

    pub fn source_grain(&self) -> u64 {
        self.source_grain
    }

    /// Positive weight enclosures in one common integer-power gauge. The aligned return
    /// chooses its rational representative jointly from these weights, never by independently
    /// normalizing probability endpoints. They remain enclosures, not exact algebraic values.
    pub(crate) fn weights_at(
        &self,
        read: &ReceivingRead,
        bits: u32,
    ) -> Result<Vec<ExactInterval>, HnnError> {
        #[cfg(test)]
        super::reuse_work::weight();
        if bits == 0 {
            return Err(HnnError::Unadmitted {
                reason: "a retained-fibre mass read needs positive enclosure precision",
            });
        }
        if read.logits.len() % 2 != 0 {
            return Err(HnnError::Shape {
                what: "an even realified receiving logit vector",
                expected: read.logits.len() + 1,
                found: read.logits.len(),
            });
        }
        let classes = read.logits.len() / 2;
        if classes == 0 || read.cells.len() != classes || read.phases.len() != classes {
            return Err(HnnError::Shape {
                what: "receiving logits, cells, and phases of one class shape",
                expected: classes,
                found: read.cells.len(),
            });
        }

        let mut terms = Vec::with_capacity(classes);
        let mut top = None::<BigInt>;
        for (class, cell) in read.cells.iter().enumerate() {
            cell.admit(self.source_grain)?;
            let expected_phase = &read.logits[2 * class + 1] / integer(2);
            if read.phases[class] != expected_phase {
                return Err(HnnError::Unadmitted {
                    reason: "a retained receiving read's phase disagrees with its imaginary logit",
                });
            }
            let (coefficient, exponent) = match &cell.fibre {
                ReceivingFibre::Rational(_) => (
                    Rat::one(),
                    cell.rational_value(self.source_grain)
                        .ok_or(HnnError::Unadmitted {
                            reason: "a rational receiving cell lost its exact full value",
                        })?,
                ),
                ReceivingFibre::Logarithmic(fibre) => {
                    if !fibre.probability.is_positive()
                        || fibre.wave != read.logits[2 * class]
                        || read_cell(&fibre.probability, &fibre.wave, self.source_grain)? != *cell
                    {
                        return Err(HnnError::Unadmitted {
                            reason: "a retained logarithmic fibre is not the canonical source read",
                        });
                    }
                    (fibre.probability.clone(), fibre.wave.clone())
                }
            };
            if !coefficient.is_positive() {
                return Err(HnnError::Unadmitted {
                    reason: "a retained-fibre mass must have a positive exact coefficient",
                });
            }
            let integer_part = exponent.floor().to_integer();
            if top.as_ref().map_or(true, |current| integer_part > *current) {
                top = Some(integer_part.clone());
            }
            terms.push((coefficient, exponent));
        }
        let top = top.expect("nonempty class shape checked above");

        let mut weights = Vec::with_capacity(classes);
        for (coefficient, exponent) in terms {
            let shifted = exponent - Rat::from_integer(top.clone());
            let power = rational_power_enclosure(&shifted, bits)?;
            let lower = coefficient.clone() * power.lower;
            let upper = coefficient * power.upper;
            if lower < Rat::zero() || upper <= Rat::zero() {
                return Err(HnnError::Unadmitted {
                    reason: "a retained-fibre weight enclosure is not positive",
                });
            }
            weights.push(ExactInterval::new(lower, upper)?);
        }
        Ok(weights)
    }

    /// The normalized class masses read from the complete retained fibre identities.
    /// `bits` controls only the exterior real-chart enclosures; it changes no retained fibre.
    pub fn masses_at(
        &self,
        read: &ReceivingRead,
        bits: u32,
    ) -> Result<Vec<ExactInterval>, HnnError> {
        let weights = self.weights_at(read, bits)?;
        normalize_weights(&weights)
    }
}

/// One finite observation produced ONLY by this receiver's authenticating weight owner.
/// It caches combined r(q,w), never the population mixture or a symbolic exact value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ProducedFibreObservation {
    source: ReceivingRead,
    receiver: RetainedFibreReceiver,
    bits: u32,
    weights: Vec<ExactInterval>,
    masses: Vec<ExactInterval>,
}
impl ProducedFibreObservation {
    pub(super) fn at(
        receiver: &RetainedFibreReceiver,
        source: &ReceivingRead,
        bits: u32,
    ) -> Result<Self, HnnError> {
        let weights = receiver.weights_at(source, bits)?;
        let masses = normalize_weights(&weights)?;
        Ok(Self {
            source: source.clone(),
            receiver: receiver.clone(),
            bits,
            weights,
            masses,
        })
    }
    pub(super) fn read_at(
        &self,
        receiver: &RetainedFibreReceiver,
        source: &ReceivingRead,
        bits: u32,
    ) -> Result<Self, HnnError> {
        if receiver != &self.receiver || source != &self.source {
            return Err(HnnError::Unadmitted {
                reason: "immutable receiving observation source/receiver mismatch",
            });
        }
        if bits == self.bits {
            Ok(self.clone())
        } else {
            Self::at(receiver, source, bits)
        }
    }
    pub(super) fn masses(&self) -> &[ExactInterval] {
        &self.masses
    }
    pub(super) fn weights(&self) -> &[ExactInterval] {
        &self.weights
    }
}
fn normalize_weights(weights: &[ExactInterval]) -> Result<Vec<ExactInterval>, HnnError> {
    #[cfg(test)]
    super::reuse_work::mass();
    let classes = weights.len();
    let mut masses = Vec::with_capacity(classes);
    for (class, weight) in weights.iter().enumerate() {
        let mut other_lower = Rat::zero();
        let mut other_upper = Rat::zero();
        for (other, candidate) in weights.iter().enumerate() {
            if other != class {
                other_lower += &candidate.lower;
                other_upper += &candidate.upper;
            }
        }
        let lower_denominator = &weight.lower + &other_upper;
        let upper_denominator = &weight.upper + &other_lower;
        if lower_denominator <= Rat::zero() || upper_denominator <= Rat::zero() {
            return Err(HnnError::Unadmitted {
                reason: "a retained-fibre normalizer enclosure must be positive",
            });
        }
        masses.push(ExactInterval::new(
            &weight.lower / lower_denominator,
            &weight.upper / upper_denominator,
        )?);
    }
    Ok(masses)
}

/// Read `2^exponent` through the scalar carried-power real chart.  The reduced denominator is the
/// exact phase grain; machine-width limits are typed refusals in this receiver.
fn rational_power_enclosure(exponent: &Rat, bits: u32) -> Result<ExactInterval, HnnError> {
    let carry = exponent.floor().to_integer();
    let fraction = exponent - Rat::from_integer(carry.clone());
    let phase = fraction.numer().to_u64().ok_or(HnnError::CountOverflow)?;
    let grain = fraction.denom().to_u64().ok_or(HnnError::CountOverflow)?;
    if grain == 0 {
        return Err(HnnError::Unadmitted {
            reason: "a rational exponent has a nonzero exact phase grain",
        });
    }
    if !grain.is_power_of_two() && u32::try_from(grain).is_err() {
        return Err(HnnError::CountOverflow);
    }
    crate::ratio::exponentiated::CarriedPower::new(carry, phase, grain)?
        .enclosure_at(bits)
        .map_err(Into::into)
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
