//! Exterior J1/J2 reader at the actual release acceptance (Refs #62 #73).
//!
//! `Delta-lambda(i,j) = V_H(i)-V_T(j)`: J1 reads H's actual producing currents;
//! J2 retains every optimal holding contact, its phase plateaus and both carry series.
//! The target starts at a clone of the same unmoved producing key, after release returns.
//! Nothing here is an operand of prediction, source ingest or deposition.
//!
//! The observed release caller passes `placement=None` to the native continuing ingest;
//! `admit_observed_cell` therefore uses `PairedObservation::encode`, without located
//! occurrence advances. J1's ordinary `phase_path` is exactly that target clock law.
//! H is never reconstructed by that static law: close/location may change its key. Its
//! per-draw current and accepted terminal current are read directly. A changed field
//! declaration is refused; no old key is extended and no absolute phase is invented.
//! These observations are transient exterior evidence, never retained HNN state.
//!
//! This consumes the helix, pair, faces and placement, and finite tower face; field
//! contacts, cell holonomy and tube remain with their owners. It avoids lessons' detached
//! demonstration, positional-lag clock and collapsed-series failures. The finite face and
//! plural-contact laws' general Lean statements remain owed in #62.

use holonics::geometry::solenoid::field::{FieldPhase, FieldPhaseError, FieldSolenoid, LockPhase};
use holonics::hnn::field::{Current, Field};
use holonics::receiver::coupling::{
    CouplingRefusal, LockReading, PhaseDifference, Strand, annotate_lock_phases, coupling32,
    payload32,
};
use num_bigint::BigInt;
use thiserror::Error;

#[derive(Debug, Error)]
enum Refusal {
    #[error("actual_field_phase: {0}")]
    Field(#[from] FieldPhaseError),
    #[error("coupling: {0}")]
    Coupling(#[from] CouplingRefusal),
    #[error("recorded_draw_path: {recorded} accepted currents for {released} released classes")]
    DrawPath { recorded: usize, released: usize },
    #[error("accepted draw has no recorded producing current")]
    MissingProducingCurrent,
}

struct Recorded {
    field: Field,
    face: FieldSolenoid,
    key: Vec<BigInt>,
    entry: FieldPhase,
    pending: Option<FieldPhase>,
    entries: Vec<FieldPhase>,
    terminal: FieldPhase,
}

/// An opt-in exterior reading. Refusals stay in the diagnostic and cannot stop the life.
pub(super) struct Trace {
    recorded: Result<Recorded, Refusal>,
}

impl Trace {
    pub(super) fn new(field: &Field, current: &Current) -> Self {
        let recorded = (|| {
            let face = FieldSolenoid::from_field(field)?;
            let entry = face.phase(field, current)?;
            Ok(Recorded {
                field: field.clone(),
                face,
                key: current.lift().to_vec(),
                terminal: entry.clone(),
                entry,
                pending: None,
                entries: Vec::new(),
            })
        })();
        Self { recorded }
    }

    /// Call after refine, at the actual producing draw, before its native continuation.
    pub(super) fn before(&mut self, field: &Field, current: &Current) {
        let error = if let Ok(recorded) = &mut self.recorded {
            match recorded.face.phase(field, current) {
                Ok(phase) => {
                    if recorded.entries.is_empty() {
                        recorded.key = current.lift().to_vec();
                        recorded.entry = phase.clone();
                        recorded.terminal = phase.clone();
                    }
                    recorded.pending = Some(phase);
                    None
                }
                Err(error) => Some(error.into()),
            }
        } else {
            None
        };
        if let Some(error) = error {
            self.recorded = Err(error);
        }
    }

    /// Only a successful native ingest contributes a class and its actual endpoint.
    pub(super) fn accepted(&mut self, field: &Field, current: &Current) {
        let error = if let Ok(recorded) = &mut self.recorded {
            match (recorded.pending.take(), recorded.face.phase(field, current)) {
                (Some(before), Ok(after)) => {
                    recorded.entries.push(before);
                    recorded.terminal = after;
                    None
                }
                (_, Err(error)) => Some(error.into()),
                (None, _) => Some(Refusal::MissingProducingCurrent),
            }
        } else {
            None
        };
        if let Some(error) = error {
            self.recorded = Err(error);
        }
    }

    pub(super) fn report(
        self,
        section: usize,
        h_whole: &[usize],
        t_whole: &[usize],
        emit: &mut dyn FnMut(String),
    ) {
        let read = (|| -> Result<_, Refusal> {
            let framed = coupling32(h_whole, t_whole)?;
            let q = &framed.coupling;
            emit(format!(
                "observed_solenoidal_coupling section={section} lambda={} F_star={} h_cells={} t_cells={} h_framing_end={} t_framing_end={} plural_contacts={} contact_plateaus={} target_used_after_release=true",
                q.lambda,
                q.least_friction,
                q.h_cells,
                q.t_cells,
                framed.h_framing_end_present,
                framed.t_framing_end_present,
                q.plural_optimal_contacts.len(),
                q.maximal_contiguous_plateaus.len(),
            ));
            let recorded = self.recorded?;
            let reading = recorded.read(h_whole, t_whole, q)?;
            Ok((recorded, reading))
        })();
        match read {
            Ok((recorded, reading)) => {
                emit(format!(
                    "observed_solenoidal_lock section={section} status=available anchor=actual_producing_current h_path=recorded_per_draw t_path=ordinary_observed_same_key key_lifts={:?} lock_rings={:?} radices={:?} radix_prime_factors={:?} modulus={} initial_lock={:?} initial_own={:?}",
                    recorded.key,
                    recorded.face.lock_rings(),
                    reading.radices,
                    recorded.face.modulus().prime_factors(),
                    reading.modulus,
                    recorded.entry.lock,
                    recorded.entry.own,
                ));
                for (index, plateau) in reading.plateaus.iter().enumerate() {
                    let carries: Vec<_> = plateau
                        .carries
                        .iter()
                        .map(|carry| {
                            (
                                carry.h_index,
                                carry.t_index,
                                &carry.h_winding,
                                &carry.t_winding,
                            )
                        })
                        .collect();
                    emit(format!(
                        "observed_solenoidal_plateau section={section} plateau={index} contact_plateau={} i={} j={} length={} first_rank={} {} paired_carry_series_i_j_h_t={carries:?}",
                        plateau.contact_plateau,
                        plateau.h_start,
                        plateau.t_start,
                        plateau.length,
                        plateau.first_rank,
                        delta_fields(&plateau.delta),
                    ));
                }
                emit(format!(
                    "observed_solenoidal_terminal section={section} F_star={} {} h_winding={} t_winding={} framing=payload_endpoint actual_whole_h_terminal_lock={:?} actual_whole_h_terminal_own={:?}",
                    reading.least_friction,
                    delta_fields(&reading.end_delta),
                    reading.h_end_winding,
                    reading.t_end_winding,
                    recorded.terminal.lock,
                    recorded.terminal.own,
                ));
            }
            Err(reason) => emit(format!(
                "observed_solenoidal_lock section={section} status=unavailable reason={reason:?}"
            )),
        }
    }
}

impl Recorded {
    fn read(
        &self,
        h_whole: &[usize],
        t_whole: &[usize],
        q: &holonics::receiver::coupling::Coupling,
    ) -> Result<LockReading, Refusal> {
        if self.entries.len() != h_whole.len() {
            return Err(Refusal::DrawPath {
                recorded: self.entries.len(),
                released: h_whole.len(),
            });
        }
        let target = payload32(t_whole, Strand::T)?;
        let t_path: Vec<LockPhase> = self
            .face
            .phase_path(&self.field, &self.key, target.cells)?
            .into_iter()
            .map(|phase| phase.lock)
            .collect();
        // Before each framing cell is also the exact endpoint of the payload prefix.
        // With no framing, the final accepted native current supplies the endpoint.
        let h_path: Vec<LockPhase> = self
            .entries
            .iter()
            .chain(std::iter::once(&self.terminal))
            .take(q.h_cells + 1)
            .map(|phase| phase.lock.clone())
            .collect();
        Ok(annotate_lock_phases(
            q,
            self.face.lock_radices(),
            &h_path,
            &t_path,
        )?)
    }
}

fn delta_fields(delta: &PhaseDifference) -> String {
    format!(
        "delta_lambda_digits={:?} delta_lambda_residue={} delta_lambda_Z_lift={} delta_lambda_whole_winding={}",
        delta.digits, delta.residue, delta.z_lift, delta.whole_winding,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::hnn::field::FieldDeclaration;

    #[test]
    fn actual_relocated_currents_are_read_instead_of_replaying_a_static_key() {
        let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
        let key: Vec<_> = field.rings().iter().map(|_| BigInt::from(7)).collect();
        let current = Current::at(&field, key.clone()).unwrap();
        let mut trace = Trace::new(&field, &current);
        let mut relocated = key.clone();
        let top = *FieldSolenoid::from_field(&field)
            .unwrap()
            .lock_rings()
            .last()
            .unwrap();
        relocated[top] += field.ring(top).period();
        let relocated = Current::at(&field, relocated).unwrap();
        trace.before(&field, &current);
        trace.accepted(&field, &relocated);
        trace.before(&field, &relocated);
        trace.accepted(&field, &relocated);
        let q = coupling32(&[1, 2], &[1, 2]).unwrap();
        let recorded = trace.recorded.as_ref().unwrap();
        let read = recorded.read(&[1, 2], &[1, 2], &q.coupling).unwrap();
        assert_eq!(q.coupling.lambda, 2);
        assert_eq!(q.coupling.least_friction, 0);
        assert_eq!(read.plateaus.len(), 2);
        assert_eq!(read.plateaus[0].delta.z_lift, BigInt::from(0));
        assert_eq!(
            read.plateaus[1].carries[0].h_winding,
            recorded
                .face
                .phase(&field, &relocated)
                .unwrap()
                .lock
                .winding
        );
        let mut lines = Vec::new();
        trace.report(3, &[1, 2], &[1, 2], &mut |line| lines.push(line));
        assert!(lines.iter().any(|line| line.contains("key_lifts=[7,")));
        assert_eq!(
            lines
                .iter()
                .filter(|line| line.starts_with("observed_solenoidal_plateau "))
                .count(),
            2
        );
        assert!(
            lines
                .iter()
                .any(|line| line.contains("paired_carry_series_i_j_h_t="))
        );
        assert!(
            lines
                .iter()
                .any(|line| line.starts_with("observed_solenoidal_terminal "))
        );
    }

    #[test]
    fn unavailable_actual_field_does_not_erase_the_exterior_coupling() {
        let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
        let current = Current::at(
            &field,
            field.rings().iter().map(|_| BigInt::from(3)).collect(),
        )
        .unwrap();
        let mut trace = Trace::new(&field, &current);
        let mut changed = field.declaration().clone();
        changed.rings[1].lock.clear();
        let changed = Field::declare(changed).unwrap();
        trace.before(&changed, &current);
        assert!(matches!(
            trace.recorded,
            Err(Refusal::Field(FieldPhaseError::DifferentField))
        ));
        let mut lines = Vec::new();
        trace.report(0, &[], &[1], &mut |line| lines.push(line));
        assert!(lines[0].contains("lambda=0 F_star=1"));
        assert!(lines[1].contains("status=unavailable reason=Field(DifferentField)"));
    }
}
