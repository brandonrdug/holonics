//! Selected forward prefixes of the actual Word (Refs #63 #62).
//!
//! Fixed executed coefficients, including chart coefficients, define an exact affine pair.
//! The input has already been imposed at the Word opening. A prefix is admitted only while
//! every internal split leaves zero remainder. The first departure is executed once by the
//! ordinary tick, and subsequent preparation starts from that actual result. Material and
//! reference crossings stay outside the Word. The serial forward remains the oracle.
//!
//! This first consumer replaces the source of each tick's input by the scanned prefix, but
//! retains the ordinary tick for that same tick's producing records and energy certificates.
//! It does not replay a forward or assert a speedup. Exact prefix preparation can cost more
//! than the serial path; receipt construction is still in causal order.

use super::*;
use crate::geometry::transport_scan::{OrderedScanError, ordered_prefixes};
use crate::ratio::linear::ExactRatMatrix;

#[cfg(test)]
mod tests;

/// Exterior scheduling evidence; not continuing state or a material covector.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ForwardSpanReading {
    pub partitions: usize,
    pub scanned_ticks: usize,
    pub serial_ticks: usize,
    pub branch_departures: usize,
    /// Gates read before an actual serial tick. Post-tick affine departures are
    /// counted separately above, because that tick already executed its owner.
    pub serial_admissions: Vec<ForwardSpanSerialAdmission>,
    /// Filled by the observed execution boundary, which owns the wall clock.
    pub elapsed_ns: Option<u128>,
}

/// One existing admission decision, returned only as exterior evidence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForwardSpanSerialAdmission {
    pub absolute_tick: usize,
    pub remaining_full_ticks: usize,
    pub nonlinear_resonator: bool,
    /// First nonzero fibre in the same order used by the admission predicate.
    /// A physical reception carry alone does not imply a nonzero split fibre.
    pub remainder: Option<ForwardSpanRemainder>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForwardSpanRemainderStream {
    Anchor,
    Storage,
    ElementDrive,
    Solve,
    Arrival,
    ContactState,
    ResonatorRate,
    ResonatorState,
}

/// An exact witness from the producing Word, never a retained state or a tolerance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForwardSpanRemainder {
    pub stream: ForwardSpanRemainderStream,
    pub owner: usize,
    /// Contact end/state component, or resonator displacement/rate component.
    /// Zero for a stream with one component per owner.
    pub component: usize,
    pub coordinate: usize,
    pub value: Rat,
}

fn first_remainder(
    stream: ForwardSpanRemainderStream,
    owner: usize,
    component: usize,
    values: &[Rat],
) -> Option<ForwardSpanRemainder> {
    values.iter().enumerate().find_map(|(coordinate, value)| {
        (!value.is_zero()).then(|| ForwardSpanRemainder {
            stream,
            owner,
            component,
            coordinate,
            value: value.clone(),
        })
    })
}

#[derive(Clone)]
struct Affine {
    a: ExactRatMatrix,
    b: Vec<Rat>,
}

impl Affine {
    fn identity(width: usize) -> Result<Self, HnnError> {
        Ok(Self {
            a: ExactRatMatrix::identity(width)?,
            b: zeros(width),
        })
    }

    /// Earlier then later: (A2 A1, A2 b1 + b2), never the commuted product.
    fn followed_by(&self, later: &Self) -> Result<Self, HnnError> {
        Ok(Self {
            a: later.a.multiply(&self.a)?,
            b: add(&later.a.apply(&self.b)?, &later.b),
        })
    }

    fn apply(&self, value: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        Ok(add(&self.a.apply(value)?, &self.b))
    }
}

fn flat(value: &EndChange) -> Vec<Rat> {
    value
        .storage
        .iter()
        .flatten()
        .chain(value.arrivals.iter().flatten().flatten())
        .chain(value.states.iter().flatten().flatten())
        .chain(value.resonators.iter().flatten().flatten().flatten())
        .cloned()
        .collect()
}

fn placed(template: &EndChange, values: &[Rat]) -> EndChange {
    let mut result = template.clone();
    let mut at = 0;
    for entry in result
        .storage
        .iter_mut()
        .flatten()
        .chain(result.arrivals.iter_mut().flatten().flatten())
        .chain(result.states.iter_mut().flatten().flatten())
        .chain(result.resonators.iter_mut().flatten().flatten().flatten())
    {
        *entry = values[at].clone();
        at += 1;
    }
    assert_eq!(
        at,
        values.len(),
        "an affine image keeps the complete declared state"
    );
    result
}

fn map(operands: &Operands, zero: &EndChange, tick: usize) -> Result<Affine, HnnError> {
    // Evaluate the already-owned local action on its basis; there is no global solve or
    // alternative state law. Unsplit preserves the executed charts, not their ideal inverses.
    let b = flat(&super::linear::tick(operands, zero, tick)?);
    let width = b.len();
    width.checked_mul(width).ok_or(HnnError::CountOverflow)?;
    let columns = (0..width)
        .map(|column| {
            let mut basis = zeros(width);
            basis[column] = integer(1);
            let image = flat(&super::linear::tick(operands, &placed(zero, &basis), tick)?);
            Ok(sub(&image, &b))
        })
        .collect::<Result<Vec<_>, HnnError>>()?;
    Ok(Affine {
        a: ExactRatMatrix::shaped(
            width,
            width,
            (0..width)
                .map(|row| {
                    (0..width)
                        .map(|column| columns[column][row].clone())
                        .collect()
                })
                .collect(),
        )?,
        b,
    })
}

impl Word<'_> {
    fn first_span_remainder(&self) -> Option<ForwardSpanRemainder> {
        use ForwardSpanRemainderStream::*;
        for (stream, rows) in [
            (Anchor, &self.carried.anchors),
            (Storage, &self.carried.storage),
            (ElementDrive, &self.carried.element_drive),
            (Solve, &self.carried.solves),
        ] {
            for (owner, values) in rows.iter().enumerate() {
                if let Some(witness) = first_remainder(stream, owner, 0, values) {
                    return Some(witness);
                }
            }
        }
        for (stream, pairs) in [
            (Arrival, &self.carried.arrivals),
            (ContactState, &self.carried.states),
        ] {
            for (owner, pair) in pairs.iter().enumerate() {
                for (component, values) in pair.iter().enumerate() {
                    if let Some(witness) = first_remainder(stream, owner, component, values) {
                        return Some(witness);
                    }
                }
            }
        }
        for (owner, resonator) in self.resonators.iter().enumerate() {
            if let Some(resonator) = resonator {
                if let Some(witness) =
                    first_remainder(ResonatorRate, owner, 0, &resonator.remainders.rate)
                {
                    return Some(witness);
                }
                for (component, values) in resonator.remainders.state.iter().enumerate() {
                    if let Some(witness) = first_remainder(ResonatorState, owner, component, values)
                    {
                        return Some(witness);
                    }
                }
            }
        }
        None
    }

    fn zero_span_remainders(&self) -> bool {
        self.first_span_remainder().is_none()
    }

    fn install_span_prefix(&mut self, prefix: EndChange) {
        self.storage = prefix.storage;
        self.arrivals = prefix.arrivals;
        self.states = prefix.states;
        for (resonance, state) in self.resonators.iter_mut().zip(prefix.resonators) {
            if let (Some(resonance), Some(state)) = (resonance, state) {
                resonance.state = state;
            }
        }
    }

    /// Execute a selected prefix scan, preserving every actual tick record and the final
    /// junction. The scan never changes a chart, a carried kernel rate or the pump origin.
    /// Nonlinear loaded laws and nonzero remainder fibres use the existing serial owner.
    pub fn forward_scanned(
        &mut self,
        phases: &ReceivingPhases,
        partitions: usize,
    ) -> Result<(Vec<Vec<Rat>>, ForwardSpanReading), HnnError> {
        if partitions == 0 {
            return Err(HnnError::Unadmitted {
                reason: "a Word span needs positive partitions",
            });
        }
        if !self.passage.is_empty() || self.ended {
            return Err(HnnError::WordEnded {
                ticks: self.passage.len(),
            });
        }
        let full_ticks = phases.junction_steps().saturating_sub(1);
        let mut reading = ForwardSpanReading {
            partitions,
            ..Default::default()
        };
        let nonlinear = self
            .operands
            .resonators()
            .iter()
            .flatten()
            .any(|r| r.material().saturation().is_some());
        while self.passage.len() < full_ticks {
            let remaining = full_ticks - self.passage.len();
            let remainder = self.first_span_remainder();
            if nonlinear || remainder.is_some() || remaining == 1 {
                reading.serial_admissions.push(ForwardSpanSerialAdmission {
                    absolute_tick: self
                        .opened_at
                        .checked_add(self.passage.len())
                        .ok_or(HnnError::CountOverflow)?,
                    remaining_full_ticks: remaining,
                    nonlinear_resonator: nonlinear,
                    remainder,
                });
                self.tick()?;
                reading.serial_ticks += 1;
                continue;
            }
            let opening = self.change()?;
            let input = flat(&opening);
            // Refuse extent overflow before constructing any basis/prefix arrays. The
            // selected caller still supplies the workload-derived outer memory/time guard.
            input
                .len()
                .checked_mul(input.len())
                .and_then(|entries| entries.checked_mul(remaining))
                .ok_or(HnnError::CountOverflow)?;
            let operands = self.operands.clone().unsplit()?;
            let zero = EndChange::rest(self.field, &operands);
            let start = self
                .opened_at
                .checked_add(self.passage.len())
                .ok_or(HnnError::CountOverflow)?;
            let ticks = (0..remaining)
                .map(|k| {
                    let tick = start.checked_add(k).ok_or(HnnError::CountOverflow)?;
                    map(&operands, &zero, tick)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let identity = Affine::identity(input.len())?;
            let prefixes = ordered_prefixes(&ticks, &identity, partitions, Affine::followed_by)
                .map_err(|error| match error {
                    OrderedScanError::ZeroPartitions => HnnError::Unadmitted {
                        reason: "a Word span needs positive partitions",
                    },
                    OrderedScanError::Composition(error) => error,
                })?;
            let mut before = opening.clone();
            for (k, prefix) in prefixes.iter().enumerate() {
                // No earlier departure can be skipped. The input is the composed prefix;
                // the same tick owner constructs its records once, rather than replaying it.
                if self.change()? != before {
                    return Err(HnnError::Unadmitted {
                        reason: "a scanned prefix must meet the actual preceding Word state",
                    });
                }
                self.install_span_prefix(before);
                self.tick()?;
                let mut after = placed(&opening, &prefix.apply(&input)?);
                for (phase, op) in after.resonator_phases.iter_mut().zip(operands.resonators()) {
                    *phase = op.as_ref().map(|op| op.phase_at(start + k));
                }
                if !self.zero_span_remainders() || self.change()? != after {
                    // This tick already is the first departing serial tick; do not execute it twice.
                    reading.serial_ticks += 1;
                    reading.branch_departures += 1;
                    break;
                }
                reading.scanned_ticks += 1;
                before = after;
            }
        }
        self.last_junction()?;
        Ok((self.receiving_anchors(phases)?, reading))
    }
}
