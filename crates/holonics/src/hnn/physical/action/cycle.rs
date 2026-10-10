//! **The cycle of a schedule: the material is read on the closed orbit of the repeated schedule**
//! (the [held-carry record](../../../../../research/records/2026-10-09_THE_ASKED_ENCOUNTER_TEACHES_THE_MATERIAL_THROUGH_ITS_HELD_CARRY.md)
//! §7d, §7g; #73, #63).
//!
//! [definition; agent-inferred, October 10] With the World key located to a point, one run of a
//! schedule ([`PhysicalReceiver::round_from`]) is an affine map of the joint opening state `x`: the
//! native opening change `χ` (every ring's storage, every contact's arrivals and states, every
//! resonator's state) and the key's state `ξ`,
//!
//! ```text
//! F(x) = M x + c,     M = ∂F/∂x  (the state tangents' columns: χ₀ = eᵢ or ψ₀ = eⱼ, no material term)
//! x*  = x_p + (I − M)⁻¹ (F(x_p) − x_p)      the closed orbit, wherever I − M is invertible
//! (I − M) δx* = δF(x*)                       the orbit's tangent along a material direction
//! dℓ_e/dθ · H = credit(T_H; r_e) + Σᵢ (δx*)ᵢ · credit(Sᵢ; r_e)   per encounter e of the orbit's run
//! ```
//!
//! where `x_p` is the present opening, `T_H` the material tangent run from `x*` with `χ₀ = 0` (on the
//! orbit the material is the one that produced the carry, so its crossing is the identity), and `Sᵢ`
//! the state tangents run from `x*`. The tangents are linear in their opening, so the orbit's credit is
//! that combination exactly.
//!
//! **Hypotheses, each checked, never assumed.**
//! - One live key with a point fibre and a declared face (the prospect's).
//! - The present opening is a received carry (an opening at rest has no carry to cross).
//! - The run is the same map at every repetition: the key's charts at the run's commits recur one run
//!   later, and the resonators' pump phases at the run's opening recur at the next. Otherwise refused.
//! - `I − M` is invertible (the closed orbit is unique). Otherwise refused.
//! - The orbit closes exactly: the run from `x*` returns to `x*`, and its state tangents give the same
//!   `M`. Otherwise refused.
//! - The run's receiving publications are joined (record §7h). On the run from `x_p` and on the orbit's
//!   run they must not move the readout `R` (nor its carrier, nor any contact): the cycle is the
//!   **fixed-readout** cycle, exact only while `R` does not move. Otherwise refused. The receiving
//!   relation's retained statistics (its Gram and chart) keep accumulating at every encounter; the
//!   cycle does not claim them still, and a later deposit that moves `R` ends it.
//!
//! **What it is not.** It claims no convergence of the actual passage to the orbit (that is the
//! spectrum of `M`, not certified here), and no settlement of `R` beyond what is measured.

use num_traits::{One, Zero};

use super::{PhysicalReceiver, ScheduledProspect};
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::ReceiverDeclaration;
use crate::hnn::word::action::PortPreparation;
use crate::hnn::word::continuation::{MaterialDirection, MaterialTangent};
use crate::hnn::word::{Absorption, EndChange, ReceptionCarry, Word, WordOpening};
use crate::hnn::Encoded;
use crate::hnn::field::FieldMaterial;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, sub};

/// [definition; agent-inferred, October 10; the record §7g] **What the cycle reads**: per encounter
/// of the orbit's run, its comparison, tangents and raw prospect; per encounter and declared
/// direction, the orbit's `(classical, phase)` credit; the orbit's opening state; and the round map's
/// dimension.
#[derive(Clone, Debug)]
pub struct CycleReading {
    pub encounters: Vec<ScheduledProspect>,
    /// `credits[e][d]`: encounter `e`, direction `d`.
    pub credits: Vec<Vec<(Rat, Rat)>>,
    /// `x*`: the native opening change's coordinates, then the key's state.
    pub orbit: Vec<Rat>,
    pub dimension: usize,
}

/// The opening change's coordinates in one exact list: every ring's storage, every contact's
/// arrivals and states, every declared resonator's state (the pump phases are the shape's own).
pub(crate) fn flatten(change: &EndChange) -> Vec<Rat> {
    let mut out: Vec<Rat> = change.storage.iter().flatten().cloned().collect();
    for [a, b] in change.arrivals.iter().chain(&change.states) {
        out.extend(a.iter().cloned());
        out.extend(b.iter().cloned());
    }
    for [a, b] in change.resonators.iter().flatten() {
        out.extend(a.iter().cloned());
        out.extend(b.iter().cloned());
    }
    out
}

/// The change of `shape`'s own shape whose coordinates are `values` ([`flatten`]'s order).
fn unflatten(shape: &EndChange, values: &[Rat]) -> Result<EndChange, HnnError> {
    let n = flatten(shape).len();
    if values.len() != n {
        return Err(HnnError::Shape {
            what: "a cycle state against its opening change's shape",
            expected: n,
            found: values.len(),
        });
    }
    let mut at = 0;
    let mut take = |len: usize| {
        let out = values[at..at + len].to_vec();
        at += len;
        out
    };
    let storage = shape.storage.iter().map(|w| take(w.len())).collect();
    let arrivals = shape
        .arrivals
        .iter()
        .map(|[a, b]| [take(a.len()), take(b.len())])
        .collect();
    let states = shape
        .states
        .iter()
        .map(|[a, b]| [take(a.len()), take(b.len())])
        .collect();
    let resonators = shape
        .resonators
        .iter()
        .map(|r| r.as_ref().map(|[a, b]| [take(a.len()), take(b.len())]))
        .collect();
    Ok(EndChange {
        storage,
        arrivals,
        states,
        resonators,
        resonator_phases: shape.resonator_phases.clone(),
    })
}

fn unit(n: usize, i: usize) -> Vec<Rat> {
    let mut v = vec![Rat::zero(); n];
    v[i] = Rat::one();
    v
}

/// A run's end, as the next run's opening state: the native opening change the end carry opens
/// (`χ`, eq. 3's crossing with the same material) followed by the key's state.
struct Opening {
    change: EndChange,
    key: Vec<Rat>,
}

impl Opening {
    fn coordinates(&self) -> Vec<Rat> {
        let mut x = flatten(&self.change);
        x.extend(self.key.iter().cloned());
        x
    }
}

impl PhysicalReceiver<'_> {
    /// The opening change of a Word opened on `opening` on `material`, before any control is
    /// prepared.
    fn opening_change(
        &self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        compared: &[bool],
        material: &Constitution,
        opening: &WordOpening,
    ) -> Result<(EndChange, Word<'_>), HnnError> {
        let (_, _, word, _) =
            self.action_opening_on(source, receiver, preparation, compared, material, opening)?;
        Ok((word.change()?, word))
    }

    /// [definition; agent-inferred, October 10; the record §7g] **The cycle of a schedule on
    /// `material`** (module header): the closed orbit of the repeated `schedule`, its run's
    /// comparisons, and, along each of `directions`, the orbit's credit at every encounter. Refused
    /// where a hypothesis of the module header fails. Nothing actual is read or written.
    #[allow(clippy::too_many_arguments)]
    pub fn world_cycle(
        &self,
        material: &Constitution,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        compared: &[bool],
        schedule: &[&[Rat]],
        directions: &[MaterialDirection],
    ) -> Result<CycleReading, HnnError> {
        let (key, start, tick) = self.located_key()?;
        let present = self.resident.reception_opening();
        let WordOpening::Received { carry: present_carry, .. } = &present else {
            return Err(HnnError::Unadmitted {
                reason: "a cycle opens on a received carry",
            });
        };
        let (shape, _) =
            self.opening_change(source, receiver, preparation, compared, material, &present)?;
        let native = flatten(&shape).len();
        let dimension = native + start.len();
        let contact = 0;
        // The state tangents: χ₀ = eᵢ over the native coordinates, then ψ₀ = eⱼ over the key's.
        let mut state_seeds = |word: &Word<'_>, ring: usize, extent: usize| {
            (0..dimension)
                .map(|i| {
                    let (chi, psi) = if i < native {
                        (unflatten(&shape, &unit(native, i))?, vec![Rat::zero(); extent])
                    } else {
                        (
                            unflatten(&shape, &vec![Rat::zero(); native])?,
                            unit(extent, i - native),
                        )
                    };
                    MaterialTangent::state_seed(word, material.commit(), contact, chi, psi, ring)
                })
                .collect::<Result<Vec<_>, _>>()
        };
        // Run 1, from the present opening: F(x_p) and M.
        let first = self.round_from(
            material,
            source,
            receiver,
            preparation,
            compared,
            schedule,
            key,
            present.clone(),
            start.clone(),
            tick,
            &mut state_seeds,
        )?;
        // The run's receiving publications (record §7h) must leave the readout as it is: the cycle is
        // the fixed-readout one, the same map at every repetition only while `R` does not move. Each
        // publication is read against the material it was deposited on (§7l): equal ends alone do
        // not certify that `R` stayed fixed within the run.
        if !first.readout_fixed || !self.same_readout(&first.material, material) {
            return Err(HnnError::Unadmitted {
                reason: "a cycle's run leaves its readout as it is: its receiving publications do not move R",
            });
        }
        let next = self.next_opening(
            source,
            receiver,
            preparation,
            compared,
            material,
            &first.end,
            first.end_state.clone(),
        )?;
        let columns = self.columns(&first.tangents, &first.end)?;
        let m = ExactRatMatrix::new(transpose(&columns, dimension))?;
        // The run is the same map at every repetition: charts and pump phases recur one run later.
        let length = first
            .end_tick
            .checked_sub(tick)
            .ok_or(HnnError::CountOverflow)?;
        let model = self.world_model().ok_or(HnnError::Unadmitted {
            reason: "a cycle reads the bound World model",
        })?;
        for t in 0..length {
            let now = tick.checked_add(t).ok_or(HnnError::CountOverflow)?;
            let later = now.checked_add(length).ok_or(HnnError::CountOverflow)?;
            if model.keys()[key].charts(now)? != model.keys()[key].charts(later)? {
                return Err(HnnError::Unadmitted {
                    reason: "a cycle's run is the same map at every repetition: the key's charts recur one run later",
                });
            }
        }
        if next.change.resonator_phases != shape.resonator_phases {
            return Err(HnnError::Unadmitted {
                reason: "a cycle's run is the same map at every repetition: the pump phases recur at the next opening",
            });
        }
        // x* = x_p + (I − M)⁻¹ (F(x_p) − x_p).
        let mut x_p = flatten(&shape);
        x_p.extend(start.iter().cloned());
        let identity = ExactRatMatrix::identity(dimension)?;
        let lifted = sub_matrix(&identity, &m)?;
        let inverse = lifted.inverse().map_err(|_| HnnError::Unadmitted {
            reason: "a cycle's closed orbit is unique: I − M is invertible",
        })?;
        let orbit = add(&x_p, &inverse.apply(&sub(&next.coordinates(), &x_p))?);
        // Open on x*: a carry whose crossing into the same material is the identity.
        let orbit_change = unflatten(&shape, &orbit[..native])?;
        let orbit_key = orbit[native..].to_vec();
        let orbit_carry = self.carry_at(
            source,
            receiver,
            preparation,
            compared,
            material,
            &present,
            present_carry,
            &orbit_change,
        )?;
        let orbit_opening = WordOpening::Received {
            carry: orbit_carry,
            absorption: Absorption::Nothing,
        };
        let (opened, _) =
            self.opening_change(source, receiver, preparation, compared, material, &orbit_opening)?;
        if flatten(&opened) != orbit[..native] {
            return Err(HnnError::Unadmitted {
                reason: "a cycle opens exactly on its orbit's state",
            });
        }
        // Run 2, from x*: the material tangents (χ₀ = 0) then the state tangents.
        let directions_count = directions.len();
        let mut seeds = |word: &Word<'_>, ring: usize, extent: usize| {
            let mut out = directions
                .iter()
                .map(|direction| {
                    MaterialTangent::held_opening(word, material.commit(), direction.clone())
                        .map(|tangent| tangent.with_port(ring, extent))
                })
                .collect::<Result<Vec<_>, _>>()?;
            out.extend(state_seeds(word, ring, extent)?);
            Ok(out)
        };
        let second = self.round_from(
            material,
            source,
            receiver,
            preparation,
            compared,
            schedule,
            key,
            orbit_opening,
            orbit_key.clone(),
            tick,
            &mut seeds,
        )?;
        let closed = self.next_opening(
            source,
            receiver,
            preparation,
            compared,
            material,
            &second.end,
            second.end_state.clone(),
        )?;
        if !second.readout_fixed || !self.same_readout(&second.material, material) {
            return Err(HnnError::Unadmitted {
                reason: "a cycle's orbit leaves its readout as it is: its receiving publications do not move R",
            });
        }
        if closed.coordinates() != orbit {
            return Err(HnnError::Unadmitted {
                reason: "a cycle's orbit closes exactly: the run from x* returns to x*",
            });
        }
        let all = self.columns(&second.tangents, &second.end)?;
        let (material_columns, state_columns) = all.split_at(directions_count);
        if ExactRatMatrix::new(transpose(state_columns, dimension))? != m {
            return Err(HnnError::Unadmitted {
                reason: "a cycle's run is affine: the state tangents give the same map from x*",
            });
        }
        // δx* = (I − M)⁻¹ δF, and the orbit's credit per encounter and direction.
        let shifts = material_columns
            .iter()
            .map(|delta| inverse.apply(delta))
            .collect::<Result<Vec<_>, _>>()?;
        let mut credits = Vec::with_capacity(second.encounters.len());
        for encounter in &second.encounters {
            let ratio = &encounter.ratio;
            let state_credits = encounter.tangents[directions_count..]
                .iter()
                .map(|t| {
                    t.comparison_credit(ratio).map(|c| {
                        (c.magnitude.clone(), &c.produced_phase + &c.observed_phase)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut per = Vec::with_capacity(directions_count);
            for (d, shift) in shifts.iter().enumerate() {
                let own = encounter.tangents[d].comparison_credit(ratio)?;
                let mut classical = own.magnitude.clone();
                let mut phase = &own.produced_phase + &own.observed_phase;
                for (s, (l, x)) in shift.iter().zip(&state_credits) {
                    classical += s * l;
                    phase += s * x;
                }
                per.push((classical, phase));
            }
            credits.push(per);
        }
        // The orbit's own run without the seeds' extra tangents in its readings.
        let encounters = second
            .encounters
            .into_iter()
            .map(|mut e| {
                e.tangents.truncate(directions_count);
                e
            })
            .collect();
        Ok(CycleReading {
            encounters,
            credits,
            orbit,
            dimension,
        })
    }

    /// The same readout on both materials: every receiving ring's receiving map and carrier equal,
    /// and the contact material untouched (a receiving publication is an observer translation).
    pub(super) fn same_readout(&self, after: &Constitution, before: &Constitution) -> bool {
        self.field.receivers().iter().all(|r| {
            after.receiving_map(r.ring) == before.receiving_map(r.ring)
                && after.receiving_carrier(r.ring) == before.receiving_carrier(r.ring)
        }) && (0..self.field.contacts().len()).all(|a| {
            after.contact_storage(a) == before.contact_storage(a)
                && after.contact_stiffness(a) == before.contact_stiffness(a)
                && after.contact_dissipation(a) == before.contact_dissipation(a)
        })
    }

    /// The next opening a run's end opens: the end carry crossed into the same material.
    #[allow(clippy::too_many_arguments)]
    fn next_opening(
        &self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        compared: &[bool],
        material: &Constitution,
        end: &ReceptionCarry,
        key: Vec<Rat>,
    ) -> Result<Opening, HnnError> {
        let opening = WordOpening::Received {
            carry: end.clone(),
            absorption: Absorption::Nothing,
        };
        let (change, _) =
            self.opening_change(source, receiver, preparation, compared, material, &opening)?;
        Ok(Opening { change, key })
    }

    /// Each tangent's column of the round map: its next opening (eq. 3) then the World's state.
    fn columns(
        &self,
        tangents: &[MaterialTangent],
        end: &ReceptionCarry,
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        tangents
            .iter()
            .map(|t| {
                let mut column = flatten(&t.opened(end, &end.conductances, self.field)?);
                column.extend(t.world().ok_or(HnnError::Unadmitted {
                    reason: "a cycle's tangents cross the World port",
                })?.iter().cloned());
                Ok(column)
            })
            .collect()
    }

    /// A carry whose crossing into `material` opens exactly `change`: the present carry's clock and
    /// conductances, `change`'s states, and the momenta `π_a = C_a w_a` (and `C_r w_r`) at the
    /// material's executed capacities, so that `C′ w′ = π` holds the rates as they are.
    #[allow(clippy::too_many_arguments)]
    fn carry_at(
        &self,
        source: &Encoded,
        receiver: &ReceiverDeclaration,
        preparation: &PortPreparation,
        compared: &[bool],
        material: &Constitution,
        present: &WordOpening,
        present_carry: &ReceptionCarry,
        change: &EndChange,
    ) -> Result<ReceptionCarry, HnnError> {
        let (_, word) =
            self.opening_change(source, receiver, preparation, compared, material, present)?;
        let operands = word.operands();
        let momenta = operands
            .contacts()
            .iter()
            .zip(&change.states)
            .map(|(c, [_, w])| c.forms().0.apply(w))
            .collect::<Result<Vec<_>, _>>()?;
        let resonator_momenta = operands
            .resonators()
            .iter()
            .zip(&change.resonators)
            .map(|(r, state)| match (r, state) {
                (Some(r), Some([_, w])) => r.material().forms().0.apply(w).map(Some),
                _ => Ok(None),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ReceptionCarry {
            change: change.clone(),
            ticks: present_carry.ticks,
            conductances: present_carry.conductances.clone(),
            momenta,
            resonator_momenta,
        })
    }
}

/// The matrix whose columns are `columns` (each of length `rows`), as row lists.
fn transpose(columns: &[Vec<Rat>], rows: usize) -> Vec<Vec<Rat>> {
    (0..rows)
        .map(|i| columns.iter().map(|c| c[i].clone()).collect())
        .collect()
}

/// `a − b`, exact.
fn sub_matrix(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Result<ExactRatMatrix, HnnError> {
    let rows = (0..a.rows())
        .map(|i| {
            (0..a.columns())
                .map(|j| Ok(a.get(i, j)? - b.get(i, j)?))
                .collect::<Result<Vec<_>, crate::ratio::linear::ExactLinearError>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(ExactRatMatrix::new(rows)?)
}

