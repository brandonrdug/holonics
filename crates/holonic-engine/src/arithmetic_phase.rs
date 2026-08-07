//! Exact prime-square phases as a bounded arithmetic application world.
//!
//! Between consecutive prime squares, the finite set of admitted prime axes
//! needed to decide primality is constant.  Crossing the next square is
//! therefore a typed rank change in valuation space, not a statistical
//! change in a scalar prime count.

use num_bigint::BigUint;
use num_traits::One;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{EventId, EventSuccessor, ExactEventLaw};
use relational_geometry::ReceiverId;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeValuation {
    pub prime: u64,
    pub exponent: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MultiplicativeSpecies {
    Prime,
    PrimeSquare { prime: u64 },
    DistinctPrimeSemiprime { left: u64, right: u64 },
    Composite,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeSquarePhase {
    pub lower_axis: u64,
    pub upper_axis: u64,
    pub lower: u64,
    pub upper: u64,
    pub admitted_axes: Vec<u64>,
    pub primorial: BigUint,
}

impl PrimeSquarePhase {
    pub fn contains(&self, value: u64) -> bool {
        self.lower <= value && value < self.upper
    }

    pub fn rank(&self) -> usize {
        self.admitted_axes.len()
    }

    pub fn survives(&self, value: u64) -> bool {
        self.admitted_axes
            .iter()
            .all(|prime| !value.is_multiple_of(*prime))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseRead {
    pub value: u64,
    pub phase: PrimeSquarePhase,
    pub valuation: Vec<PrimeValuation>,
    pub survivor: bool,
    pub species: MultiplicativeSpecies,
}

/// The exact wall at `admitted_axis²`. The lower phase does not disappear:
/// its axes embed as the initial axes of the higher-rank phase.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseBoundary {
    pub value: u64,
    pub admitted_axis: u64,
    pub before: PrimeSquarePhase,
    pub after: PrimeSquarePhase,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeAxisReceiver {
    pub receiver: ReceiverId,
    pub prime_axis: u64,
    pub source_event: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseStanding {
    pub value: u64,
    pub phase: PrimeSquarePhase,
    pub receivers: Vec<PrimeAxisReceiver>,
    pub next_receiver: u64,
}

impl PrimePhaseStanding {
    pub fn new(
        value: u64,
        source_event: EventId,
        first_receiver: ReceiverId,
    ) -> Result<Self, PrimePhaseError> {
        let phase = prime_square_phase(value)?;
        let mut next_receiver = first_receiver.0;
        let mut receivers = Vec::with_capacity(phase.admitted_axes.len());
        for prime_axis in &phase.admitted_axes {
            receivers.push(PrimeAxisReceiver {
                receiver: ReceiverId(next_receiver),
                prime_axis: *prime_axis,
                source_event,
            });
            next_receiver = next_receiver
                .checked_add(1)
                .ok_or(PrimePhaseError::CarrierOverflow)?;
        }
        Ok(Self {
            value,
            phase,
            receivers,
            next_receiver,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseEvent {
    pub event: EventId,
    pub value: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimePhaseRadiation {
    pub event: EventId,
    pub read: PrimePhaseRead,
    pub boundary: Option<PrimePhaseBoundary>,
    pub founded_receiver: Option<PrimeAxisReceiver>,
}

/// Integer succession as an exact application law. The receiver population
/// is the admitted valuation-axis population; it grows only when the source
/// crosses an actual prime-square wall.
#[derive(Clone, Copy, Debug, Default)]
pub struct PrimePhaseLaw;

impl ExactEventLaw for PrimePhaseLaw {
    type Standing = PrimePhaseStanding;
    type Event = PrimePhaseEvent;
    type Radiation = PrimePhaseRadiation;
    type Error = PrimePhaseError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let expected = standing_before
            .value
            .checked_add(1)
            .ok_or(PrimePhaseError::CarrierOverflow)?;
        if event.value != expected {
            return Err(PrimePhaseError::NonSuccessor {
                expected,
                supplied: event.value,
            });
        }
        let read = read_prime_phase(event.value)?;
        let boundary = prime_phase_boundary(event.value)?;
        let mut standing_after = standing_before.clone();
        standing_after.value = event.value;
        standing_after.phase = read.phase.clone();
        let founded_receiver = if let Some(boundary) = &boundary {
            let receiver = PrimeAxisReceiver {
                receiver: ReceiverId(standing_after.next_receiver),
                prime_axis: boundary.admitted_axis,
                source_event: event.event,
            };
            standing_after.next_receiver = standing_after
                .next_receiver
                .checked_add(1)
                .ok_or(PrimePhaseError::CarrierOverflow)?;
            standing_after.receivers.push(receiver.clone());
            Some(receiver)
        } else {
            None
        };
        debug_assert_eq!(
            standing_after
                .receivers
                .iter()
                .map(|receiver| receiver.prime_axis)
                .collect::<Vec<_>>(),
            standing_after.phase.admitted_axes,
        );
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![PrimePhaseRadiation {
                event: event.event,
                read,
                boundary,
                founded_receiver,
            }],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PrimePhaseError {
    #[error("prime-square phases begin at 2²=4, got {0}")]
    BelowFirstPhase(u64),
    #[error("the requested exact u64 prime-square boundary exceeds the carrier")]
    CarrierOverflow,
    #[error("integer succession expected {expected}, but the source supplied {supplied}")]
    NonSuccessor { expected: u64, supplied: u64 },
}

pub fn prime_square_phase(value: u64) -> Result<PrimeSquarePhase, PrimePhaseError> {
    if value < 4 {
        return Err(PrimePhaseError::BelowFirstPhase(value));
    }
    let mut primes = vec![2_u64];
    let mut candidate = 3_u64;
    loop {
        if is_prime_from_axes(candidate, &primes) {
            primes.push(candidate);
            let upper = candidate
                .checked_mul(candidate)
                .ok_or(PrimePhaseError::CarrierOverflow)?;
            let lower_axis = primes[primes.len() - 2];
            let lower = lower_axis
                .checked_mul(lower_axis)
                .ok_or(PrimePhaseError::CarrierOverflow)?;
            if value < upper {
                let admitted_axes = primes[..primes.len() - 1].to_vec();
                let primorial = admitted_axes
                    .iter()
                    .fold(BigUint::one(), |product, prime| product * *prime);
                return Ok(PrimeSquarePhase {
                    lower_axis,
                    upper_axis: candidate,
                    lower,
                    upper,
                    admitted_axes,
                    primorial,
                });
            }
        }
        candidate = candidate
            .checked_add(2)
            .ok_or(PrimePhaseError::CarrierOverflow)?;
    }
}

pub fn read_prime_phase(value: u64) -> Result<PrimePhaseRead, PrimePhaseError> {
    let phase = prime_square_phase(value)?;
    let valuation = factor(value);
    let species = match valuation.as_slice() {
        [PrimeValuation { exponent: 1, .. }] => MultiplicativeSpecies::Prime,
        [PrimeValuation { prime, exponent: 2 }] => {
            MultiplicativeSpecies::PrimeSquare { prime: *prime }
        }
        [
            PrimeValuation {
                prime: left,
                exponent: 1,
            },
            PrimeValuation {
                prime: right,
                exponent: 1,
            },
        ] => MultiplicativeSpecies::DistinctPrimeSemiprime {
            left: *left,
            right: *right,
        },
        _ => MultiplicativeSpecies::Composite,
    };
    let survivor = phase.survives(value);
    Ok(PrimePhaseRead {
        value,
        phase,
        valuation,
        survivor,
        species,
    })
}

pub fn prime_phase_boundary(value: u64) -> Result<Option<PrimePhaseBoundary>, PrimePhaseError> {
    let after = prime_square_phase(value)?;
    if value != after.lower || after.lower_axis == 2 {
        return Ok(None);
    }
    let before = prime_square_phase(value - 1)?;
    Ok(Some(PrimePhaseBoundary {
        value,
        admitted_axis: after.lower_axis,
        before,
        after,
    }))
}

pub fn factor(mut value: u64) -> Vec<PrimeValuation> {
    let mut factors = Vec::new();
    let mut prime = 2_u64;
    while prime <= value / prime {
        if value.is_multiple_of(prime) {
            let mut exponent = 0_u32;
            while value.is_multiple_of(prime) {
                value /= prime;
                exponent += 1;
            }
            factors.push(PrimeValuation { prime, exponent });
        }
        prime = if prime == 2 { 3 } else { prime + 2 };
    }
    if value > 1 {
        factors.push(PrimeValuation {
            prime: value,
            exponent: 1,
        });
    }
    factors
}

fn is_prime_from_axes(candidate: u64, primes: &[u64]) -> bool {
    primes
        .iter()
        .take_while(|prime| **prime <= candidate / **prime)
        .all(|prime| !candidate.is_multiple_of(*prime))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalWorld;

    #[test]
    fn forty_nine_to_one_twenty_one_is_one_exact_rank_four_phase() {
        for value in 49..121 {
            let read = read_prime_phase(value).unwrap();
            assert_eq!(read.phase.admitted_axes, vec![2, 3, 5, 7]);
            assert_eq!(read.phase.primorial, BigUint::from(210_u16));
            assert_eq!(
                read.survivor,
                matches!(read.species, MultiplicativeSpecies::Prime),
                "prime-square theorem failed at {value}",
            );
        }
    }

    #[test]
    fn a_prime_square_wall_adds_one_axis_and_preserves_the_old_prefix() {
        let wall = prime_phase_boundary(121).unwrap().unwrap();
        assert_eq!(wall.admitted_axis, 11);
        assert_eq!(wall.before.admitted_axes, vec![2, 3, 5, 7]);
        assert_eq!(wall.after.admitted_axes, vec![2, 3, 5, 7, 11]);
        assert_eq!(
            wall.after.admitted_axes[..wall.before.rank()],
            wall.before.admitted_axes,
        );
        assert_eq!(
            read_prime_phase(121).unwrap().species,
            MultiplicativeSpecies::PrimeSquare { prime: 11 },
        );
    }

    #[test]
    fn prime_square_and_distinct_semiprime_keep_distinct_faces() {
        assert_eq!(
            read_prime_phase(49).unwrap().species,
            MultiplicativeSpecies::PrimeSquare { prime: 7 },
        );
        assert_eq!(
            read_prime_phase(77).unwrap().species,
            MultiplicativeSpecies::DistinctPrimeSemiprime { left: 7, right: 11 },
        );
    }

    #[test]
    fn arithmetic_succession_founds_one_receiver_at_the_prime_square_wall() {
        let standing = PrimePhaseStanding::new(120, EventId(1), ReceiverId(20)).unwrap();
        assert_eq!(standing.receivers.len(), 4);
        let mut world = CausalWorld::new(PrimePhaseLaw, standing);
        let radiation = world
            .receive(&PrimePhaseEvent {
                event: EventId(2),
                value: 121,
            })
            .unwrap()
            .radiation
            .remove(0);
        assert_eq!(
            radiation.founded_receiver,
            Some(PrimeAxisReceiver {
                receiver: ReceiverId(24),
                prime_axis: 11,
                source_event: EventId(2),
            }),
        );
        assert_eq!(world.standing().receivers.len(), 5);
        assert_eq!(
            world
                .standing()
                .receivers
                .iter()
                .map(|receiver| receiver.prime_axis)
                .collect::<Vec<_>>(),
            vec![2, 3, 5, 7, 11],
        );
    }
}
