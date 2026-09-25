//! **Joint reception: an interaction that changes both participants and returns the receipt.**
//!
//! [definition] To receive is to measure and compare
//! ([§10](../../../../docs/ELEMENTARY_OBJECTS.md#10-receipt)): reception is an interaction
//! `I_C(|H_S⟩, |H_R⟩) = (|H'_S⟩, |H'_R⟩, f_R)` that changes both participants. A source and a
//! receiver are joined in one Holon law ([`JointLaw`]): a [`ReferenceHolon`] whose storage splits
//! as source ⊕ receiver with no cross block, so the stored energy is the two participants' own
//! (`Holarchy/Reception.JointLaw.Q`). The joint law of two Holons joined at ports is a
//! Holarchy's whole ([`JointLaw::of_holarchy`]). One admitted joint step **is solved** from the
//! law, never taken as an input: the Dirac-form implicit-midpoint step of
//! [`ReferenceHolon::commit`], refused with `NotUniquelySolvable` or `Inconsistent` exactly when
//! the step does not determine the motion (Lean `Holarchy/Reception.interact`, `interact_ok_iff`:
//! a singular step matrix `1 − (h/2)(J − R)Q` is refused).
//!
//! [`JointLaw::interact`] returns an [`InteractionReturn`]: both participants' next states, the
//! receiver's face and its motion, the receipt, the port bond at the external ports (the supply
//! and the pulled-back midpoint effort, Lean `InteractionReturn.boundaryBond`), the stored energy of each
//! participant before and after, the certified balance and the unresolved fibre. The face is `ρ(t, x_S, x_R) = C_S x_S + C_R x_R + o + t·c` ([`ReceiverFace`]); over the
//! solved step its change splits exactly into the source's motion, the receiver's own motion and
//! the chart's explicit motion, `Δy = C_S Δx_S + C_R Δx_R + h c`, the discrete moving-receiver
//! rate on the law's own field ([`FaceMotion`]).
//!
//! [definition] **`HolonLaw::receive` is the zero-storage specialization**
//! ([`JointLaw::reading`], `Holarchy/Reception.zero_storage_receiver_is_passive_reading`). A
//! receiver that stores nothing, coupled at the source's storage efforts by `C` (`ẋ_R = C ē_S`,
//! and `Cᵀ ē_R` back into the source), has zero effort, so it exerts no back-action: the source
//! advances by its own law, the receiver changes by `h C ē_S`, the bond it presents to the source
//! is a passive-coholon bond of zero power, and the joint balance is the source's own.
//!
//! | Lean `Holarchy/Reception` | Rust |
//! |---|---|
//! | `JointLaw`, `JointLaw.Q`, `stepMatrix`, `stepSource`, `jointStep_iff`, `solveStep_unique` | [`JointLaw`], [`JointLaw::interact`] |
//! | `interact`, `interact_ok_iff`, `interact_solves`, `StepRefusal.singular`, `singular_step_refused` | [`JointLaw::interact`] |
//! | `InteractionReturn`, `readStep`, `boundaryBond_power` | [`InteractionReturn`], [`InteractionReturn::boundary`] |
//! | `InteractionReturn.balance`, `readStep_stored_split` | [`InteractionReturn::balance`], [`InteractionReturn::stored_before`] |
//! | `readStep_passive`, `active_element_is_not_passive` | tests |
//! | `readStep_unresolved_face`, `unresolved_fibre_is_plural` | [`UnresolvedFibre`] |
//! | `JointLaw.field`, `moving_receiver_rate_of_law` | [`FaceMotion`] |
//! | `zero_storage_receiver_is_passive_reading` | [`JointLaw::reading`], [`crate::holon::law::HolonLaw::receive`] |
//! | `reception_changes_both` | test |
//!
//! [open] The Rust law goes beyond Lean's `JointLaw` `ẋ = (J − R)Qx + Bu`: it is any Dirac
//! structure in kernel form with active relation and pump schedule, whose balance carries the
//! active power, the deposition work and the discretization defect, and its external ports take
//! the supply as effort, so the port bond is `(Bᵀē, u)` with the roles of Lean's `(u, Bᵀē)`
//! exchanged (the same power). A refusal names the nullity or the inconsistency where Lean's
//! `StepRefusal.singular` carries a kernel vector. [`FaceMotion`] is the exact discrete instance of
//! `moving_receiver_rate_of_law` for an affine face over the solved midpoint step
//! (`Δy = C_S Δx_S + C_R Δx_R + h c`). The Dirac-form joint step and the discrete face law are owed
//! in #62.

use num_traits::{One, Zero};

use crate::holarchy::Holarchy;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{Pump, PumpSchedule};
use crate::holon::law::{EnergyBalance, HolonLaw, ReferenceHolon, Scheme};
use crate::holon::port::Bond;
use crate::holon::{Holon, HolonError, HolonState, PortCounts, PortHolon};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::{
    add, at, form_matrix, matrix, matrix_form, scale, sub, submatrix,
};
use crate::receiver::receipt::{Receipt, ReceiptLaw};

/// [definition] **The joint law of a source and a receiver**: a Holon law whose storage splits as
/// the first `source` coordinates and the rest, with no cross block at any commit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointLaw {
    law: ReferenceHolon,
    source: usize,
}

impl JointLaw {
    /// Refuses a split beyond the storage, or a storage form (declared or scheduled) that couples
    /// the source and the receiver.
    pub fn new(law: ReferenceHolon, source: usize) -> Result<Self, HolonError> {
        let holon = law.holon();
        let sigma = holon.port_holon().counts().storage;
        if source > sigma {
            return Err(HolonError::Shape {
                what: "source storage extent",
                expected: sigma,
                found: source,
            });
        }
        let period = holon.pump().map_or(1, |pump| pump.schedule.period()) as u64;
        for commit in 0..period {
            let form = holon.storage_at(commit);
            for i in 0..source {
                for j in source..sigma {
                    if !form.at(i, j).is_zero() {
                        return Err(HolonError::Unsupported {
                            what: "a joint law",
                            reason: "its storage couples the source and the receiver",
                        });
                    }
                }
            }
        }
        Ok(Self { law, source })
    }

    /// **The pair joined in a Holarchy**: the whole's law at a declared step and scheme, the left
    /// constituent the source and the right the receiver (the whole's storage is their block).
    pub fn of_holarchy(holarchy: &Holarchy, step: Rat, scheme: Scheme) -> Result<Self, HolonError> {
        Self::new(
            ReferenceHolon::new(holarchy.whole().clone(), step, scheme)?,
            holarchy.left().port_holon().counts().storage,
        )
    }

    /// [definition] **The zero-storage reading receiver** of a source law
    /// (`Holarchy/Reception.zero_storage_receiver_is_passive_reading`): `reader.rows()` receiver
    /// coordinates with zero storage, coupled at the source's storage efforts by the skew pair
    /// `ẋ_R = C ē_S`, `ẋ_S += −Cᵀ ē_R`. The joint structure is the source's Dirac structure with
    /// the source storage flow read as `f_S − Cᵀ e_R`, plus the rows `f_R + C e_S = 0`; it is
    /// re-certified Dirac. Named ports, the complex and the navigators stay with the source.
    pub fn reading(source: &ReferenceHolon, reader: &ExactRatMatrix) -> Result<Self, HolonError> {
        let holon = source.holon();
        let port_holon = holon.port_holon();
        let c = port_holon.counts();
        if reader.columns() != c.storage {
            return Err(HolonError::Shape {
                what: "reader columns (source storage)",
                expected: c.storage,
                found: reader.columns(),
            });
        }
        let (sigma, receivers, n) = (c.storage, reader.rows(), c.total());
        let form = port_holon.dirac().form();
        let (f, e) = (form.flow_matrix()?, form.effort_matrix()?);
        let (rows, ports) = (f.rows() + receivers, n + receivers);
        // Joint port j: source storage (j < σ), receiver storage (σ ≤ j < σ + r), then the rest.
        let old = |j: usize| -> Option<usize> {
            if j < sigma {
                Some(j)
            } else if j < sigma + receivers {
                None
            } else {
                Some(j - receivers)
            }
        };
        let flow = matrix(rows, ports, |row, j| {
            if row < f.rows() {
                old(j).map_or(Rat::zero(), |p| at(&f, row, p))
            } else if j == sigma + (row - f.rows()) {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let effort = matrix(rows, ports, |row, j| {
            if row < f.rows() {
                match old(j) {
                    Some(p) => at(&e, row, p),
                    // −(F_S Cᵀ)_(row, j−σ): the source flow read as f_S − Cᵀ e_R.
                    None => (0..sigma).fold(Rat::zero(), |sum, i| {
                        sum - at(&f, row, i) * at(reader, j - sigma, i)
                    }),
                }
            } else if j < sigma {
                at(reader, row - f.rows(), j)
            } else {
                Rat::zero()
            }
        })?;
        let widen = |form: &SymmetricForm| form.direct_sum(&SymmetricForm::zeros(receivers));
        let joint = PortHolon::new(
            DiracStructure::kernel_form(&flow, &effort)?,
            PortCounts {
                storage: sigma + receivers,
                ..c
            },
            widen(port_holon.storage()),
            port_holon.resistance().clone(),
        )?;
        let mut joint = Holon::new(joint)?.with_active(holon.active().clone())?;
        if let Some(pump) = holon.pump() {
            let forms = (0..pump.schedule.period() as u64)
                .map(|commit| widen(pump.schedule.storage_at(commit)))
                .collect();
            joint = joint.with_pump(Pump {
                schedule: PumpSchedule::new(forms)?,
                clock: pump.clock.clone(),
            })?;
        }
        Self::new(
            ReferenceHolon::new(joint, source.step().clone(), source.scheme())?,
            sigma,
        )
    }

    pub fn law(&self) -> &ReferenceHolon {
        &self.law
    }

    pub fn source_extent(&self) -> usize {
        self.source
    }

    pub fn receiver_extent(&self) -> usize {
        self.law.holon().port_holon().counts().storage - self.source
    }

    /// Each participant's own stored energy under the storage in force at a commit.
    fn stored(&self, configuration: &[Rat], commit: u64) -> Result<StoredEnergy, HolonError> {
        let q = form_matrix(self.law.holon().storage_at(commit));
        let sigma = configuration.len();
        let source: Vec<usize> = (0..self.source).collect();
        let receiver: Vec<usize> = (self.source..sigma).collect();
        let energy = |indices: &[usize]| -> Result<Rat, HolonError> {
            let block = matrix_form(&submatrix(&q, indices, indices)?)?;
            let x: Vec<Rat> = indices.iter().map(|i| configuration[*i].clone()).collect();
            crate::holon::element::storage_energy(&block, &x)
        };
        Ok(StoredEnergy {
            source: energy(&source)?,
            receiver: energy(&receiver)?,
        })
    }

    /// [proved-derived; implemented-exact] **Joint reception** (Lean `Holarchy/Reception.interact`,
    /// `interact_solves`): solve one step of the joint law from `state` (source ⊕ receiver) under
    /// the external efforts `input`, refuse a step that does not determine the motion
    /// (`interact_ok_iff`) or whose balance does not close, and return what the interaction
    /// returns.
    pub fn interact(
        &self,
        state: &HolonState,
        input: &[Rat],
        face: &ReceiverFace,
        receipt: &ReceiptLaw,
    ) -> Result<InteractionReturn, HolonError> {
        let (sigma_s, sigma_r) = (self.source, self.receiver_extent());
        if face.source.columns() != sigma_s || face.receiver.columns() != sigma_r {
            return Err(HolonError::Shape {
                what: "receiver face columns (source ⊕ receiver)",
                expected: sigma_s + sigma_r,
                found: face.source.columns() + face.receiver.columns(),
            });
        }
        let advance = self.law.advance(state, input)?;
        if !advance.balance.is_exact() {
            return Err(HolonError::ConformanceFailed {
                what: "the joint balance closes",
            });
        }
        let before = &state.configuration;
        let after = &advance.state.configuration;
        let (source_before, receiver_before) = before.split_at(sigma_s);
        let (source_after, receiver_after) = after.split_at(sigma_s);
        let motion = FaceMotion {
            source: face.source.apply(&sub(source_after, source_before))?,
            receiver: face.receiver.apply(&sub(receiver_after, receiver_before))?,
            chart: scale(self.law.step(), &face.chart_rate),
        };
        let face_after = add(
            &face.read(source_before, receiver_before)?,
            &add(&add(&motion.source, &motion.receiver), &motion.chart),
        );
        let directions = face.receiver.kernel_basis()?;
        Ok(InteractionReturn {
            next_source: source_after.to_vec(),
            next_receiver: receiver_after.to_vec(),
            commit: advance.state.commit,
            face: face_after,
            face_motion: motion,
            receipt: receipt.receive(after)?,
            boundary: self.law.kinds(&advance)?.external,
            stored_before: self.stored(before, state.commit)?,
            stored_after: self.stored(after, advance.state.commit)?,
            balance: advance.balance,
            unresolved: UnresolvedFibre {
                point: receiver_after.to_vec(),
                directions,
            },
        })
    }
}

/// [definition] **A moving receiver's face** `ρ(t, x_S, x_R) = C_S x_S + C_R x_R + o + t·c`: it
/// reads the source, its own state and its chart's explicit motion `c = ∂_t ρ`, read from the
/// step's start.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverFace {
    source: ExactRatMatrix,
    receiver: ExactRatMatrix,
    offset: Vec<Rat>,
    chart_rate: Vec<Rat>,
}

impl ReceiverFace {
    pub fn new(
        source: ExactRatMatrix,
        receiver: ExactRatMatrix,
        offset: Vec<Rat>,
        chart_rate: Vec<Rat>,
    ) -> Result<Self, HolonError> {
        let rows = source.rows();
        for (found, what) in [
            (receiver.rows(), "receiver face rows"),
            (offset.len(), "face offset"),
            (chart_rate.len(), "face chart rate"),
        ] {
            if found != rows {
                return Err(HolonError::Shape {
                    what,
                    expected: rows,
                    found,
                });
            }
        }
        Ok(Self {
            source,
            receiver,
            offset,
            chart_rate,
        })
    }

    /// The face that reads the receiver's own state and nothing else.
    pub fn receiver_state(source: usize, receiver: usize) -> Result<Self, HolonError> {
        Self::new(
            ExactRatMatrix::zero(receiver, source)?,
            ExactRatMatrix::identity(receiver)?,
            vec![Rat::zero(); receiver],
            vec![Rat::zero(); receiver],
        )
    }

    /// The face at the step's start.
    pub fn read(&self, source: &[Rat], receiver: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        Ok(add(
            &add(&self.source.apply(source)?, &self.receiver.apply(receiver)?),
            &self.offset,
        ))
    }
}

/// [definition] **The face's motion over the solved step**, split into the three terms of the
/// moving-receiver rate: `C_S Δx_S` (the source's motion), `C_R Δx_R` (the receiver's own motion)
/// and `h c` (the chart's explicit motion). Their sum is the face's change, exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaceMotion {
    pub source: Vec<Rat>,
    pub receiver: Vec<Rat>,
    pub chart: Vec<Rat>,
}

/// [definition] Each participant's own stored energy; the joint storage is their sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StoredEnergy {
    pub source: Rat,
    pub receiver: Rat,
}

impl StoredEnergy {
    pub fn joint(&self) -> Rat {
        &self.source + &self.receiver
    }
}

/// [definition] **The unresolved fibre**: the receiver states the face does not separate from the
/// reached one, `x_R⁺ + ker C_R` (Lean `Holarchy/Reception.readStep_unresolved_face`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnresolvedFibre {
    pub point: Vec<Rat>,
    pub directions: Vec<Vec<Rat>>,
}

/// [definition] **What an interaction returns** (Lean `Holarchy/Reception.InteractionReturn`). Only
/// [`JointLaw::interact`] builds one, and only when the balance closes, so the balance is
/// certified.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InteractionReturn {
    next_source: Vec<Rat>,
    next_receiver: Vec<Rat>,
    commit: u64,
    face: Vec<Rat>,
    face_motion: FaceMotion,
    receipt: Receipt,
    boundary: Bond,
    stored_before: StoredEnergy,
    stored_after: StoredEnergy,
    balance: EnergyBalance,
    unresolved: UnresolvedFibre,
}

impl InteractionReturn {
    pub fn next_source(&self) -> &[Rat] {
        &self.next_source
    }

    pub fn next_receiver(&self) -> &[Rat] {
        &self.next_receiver
    }

    /// The joint commit reached.
    pub fn commit(&self) -> u64 {
        self.commit
    }

    /// The receiver's face at the reached state.
    pub fn face(&self) -> &[Rat] {
        &self.face
    }

    pub fn face_motion(&self) -> &FaceMotion {
        &self.face_motion
    }

    pub fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    /// The port bond at the external ports: flow `Bᵀ ē` against the declared effort `u`, whose
    /// power times the step is the supplied energy (Lean `boundaryBond_power`).
    pub fn boundary(&self) -> &Bond {
        &self.boundary
    }

    pub fn stored_before(&self) -> &StoredEnergy {
        &self.stored_before
    }

    pub fn stored_after(&self) -> &StoredEnergy {
        &self.stored_after
    }

    /// The certified balance: `stored_change = −dissipated + port + active + deposition_work +
    /// discretization_defect`, residual zero.
    pub fn balance(&self) -> &EnergyBalance {
        &self.balance
    }

    pub fn unresolved(&self) -> &UnresolvedFibre {
        &self.unresolved
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Signed;

    use super::*;
    use crate::holarchy::Gluing;
    use crate::holon::element::ActiveRelation;
    use crate::ratio::linear::vector::{integer_matrix, ints};
    use crate::ratio::{integer, rat};
    use crate::receiver::receipt::RegionChart;

    fn zero(rows: usize, columns: usize) -> ExactRatMatrix {
        ExactRatMatrix::zero(rows, columns).unwrap()
    }

    fn joint(
        coupling: &[&[i64]],
        resistance: &ExactRatMatrix,
        input: &ExactRatMatrix,
        active: Option<ExactRatMatrix>,
    ) -> JointLaw {
        let omega = integer_matrix(coupling).unwrap();
        let n = omega.rows();
        let port_holon = PortHolon::medium(
            &omega,
            resistance,
            SymmetricForm::from_diagonal(vec![integer(1); n]),
            input,
            active.is_some(),
        )
        .unwrap();
        let mut holon = Holon::new(port_holon).unwrap();
        if let Some(active) = active {
            holon = holon
                .with_active(ActiveRelation::new(active).unwrap())
                .unwrap();
        }
        JointLaw::new(
            ReferenceHolon::new(holon, integer(1), Scheme::Midpoint).unwrap(),
            1,
        )
        .unwrap()
    }

    fn no_receipt(extent: usize) -> ReceiptLaw {
        ReceiptLaw::new(extent, Vec::new(), Vec::new()).unwrap()
    }

    /// `Holarchy/Reception.InteractionReturn.balance`, `readStep_stored_split`, `boundaryBond_power`:
    /// two media joined
    /// at a shared port form a Holarchy whose whole is the joint law; its solved step's balance
    /// closes and the stored energy is the two participants' own before and after.
    #[test]
    fn joint_reception_balances_and_splits_the_stored_energy() {
        let medium = |g: i64| {
            Holon::new(
                PortHolon::medium(
                    &zero(1, 1),
                    &integer_matrix(&[&[1]]).unwrap(),
                    SymmetricForm::from_diagonal(vec![integer(g)]),
                    &integer_matrix(&[&[1, 1]]).unwrap(),
                    false,
                )
                .unwrap(),
            )
            .unwrap()
        };
        let holarchy = medium(2)
            .interconnect(&medium(3), &Gluing::at_ports(vec![(1, 0)]).unwrap())
            .unwrap();
        let law = JointLaw::of_holarchy(&holarchy, rat(1, 2), Scheme::Midpoint).unwrap();
        let state = HolonState::new(ints(&[3, -1]));
        let returned = law
            .interact(
                &state,
                &ints(&[2, -1]),
                &ReceiverFace::receiver_state(1, 1).unwrap(),
                &no_receipt(2),
            )
            .unwrap();
        let energy = |x: &[Rat], commit| {
            crate::holon::element::storage_energy(law.law().holon().storage_at(commit), x).unwrap()
        };
        let mut after = returned.next_source().to_vec();
        after.extend_from_slice(returned.next_receiver());
        assert_eq!(
            returned.stored_before().joint(),
            energy(&state.configuration, 0)
        );
        assert_eq!(returned.stored_after().joint(), energy(&after, 1));
        assert_eq!(
            returned.stored_after().joint() - returned.stored_before().joint(),
            returned.balance().stored_change
        );
        assert!(returned.balance().is_exact());
        assert_eq!(
            returned.balance().port,
            law.law().step() * returned.boundary().power()
        );
    }

    /// `Holarchy/Reception.readStep_passive`: with a certified resistance, a passive active
    /// relation and no pump, the solved step's stored energy grows by no more than the supply.
    #[test]
    fn a_passive_joint_step_stores_no_more_than_it_is_supplied() {
        let law = joint(
            &[&[0, -1], &[1, 0]],
            &integer_matrix(&[&[1, 0], &[0, 2]]).unwrap(),
            &integer_matrix(&[&[1], &[0]]).unwrap(),
            None,
        );
        let returned = law
            .interact(
                &HolonState::new(ints(&[1, 2])),
                &ints(&[3]),
                &ReceiverFace::receiver_state(1, 1).unwrap(),
                &no_receipt(2),
            )
            .unwrap();
        let grown = returned.stored_after().joint() - returned.stored_before().joint();
        assert!(returned.balance().dissipated.is_positive());
        assert!(grown <= returned.balance().port);
    }

    /// `Holarchy/Reception.active_element_is_not_passive`: an active relation `L = 1` triples the
    /// state from `(1, 0)` with nothing supplied; the stored energy grows `1/2 → 9/2` beyond the
    /// zero supply, and the balance still closes with active power `4`.
    #[test]
    fn an_active_element_is_not_passive() {
        let law = joint(
            &[&[0, 0], &[0, 0]],
            &zero(2, 2),
            &zero(2, 0),
            Some(ExactRatMatrix::identity(2).unwrap()),
        );
        let returned = law
            .interact(
                &HolonState::new(ints(&[1, 0])),
                &[],
                &ReceiverFace::receiver_state(1, 1).unwrap(),
                &no_receipt(2),
            )
            .unwrap();
        assert_eq!(returned.next_source(), &ints(&[3]));
        assert_eq!(returned.stored_before().joint(), rat(1, 2));
        assert_eq!(returned.stored_after().joint(), rat(9, 2));
        assert_eq!(returned.balance().active, integer(4));
        assert!(returned.balance().port.is_zero());
        assert!(returned.stored_after().joint() - returned.stored_before().joint() > Rat::zero());
    }

    /// `Holarchy/Reception.reception_changes_both`: a source at `1` and a receiver at `0` joined by
    /// a gyrator move to `3/5` and `4/5`; the receiver gains exactly the `8/25` the source loses,
    /// with nothing supplied or dissipated. The receipt reads the reached joint state.
    #[test]
    fn reception_changes_both_participants() {
        let law = joint(&[&[0, -1], &[1, 0]], &zero(2, 2), &zero(2, 0), None);
        let receipt = ReceiptLaw::new(2, vec![ints(&[0, 5])], vec![RegionChart::rate()]).unwrap();
        let returned = law
            .interact(
                &HolonState::new(ints(&[1, 0])),
                &[],
                &ReceiverFace::receiver_state(1, 1).unwrap(),
                &receipt,
            )
            .unwrap();
        assert_eq!(returned.next_source(), &[rat(3, 5)]);
        assert_eq!(returned.next_receiver(), &[rat(4, 5)]);
        assert_eq!(returned.face(), &[rat(4, 5)]);
        assert_eq!(
            returned.stored_after().source.clone() - returned.stored_before().source.clone(),
            rat(-8, 25)
        );
        assert_eq!(
            returned.stored_after().receiver.clone() - returned.stored_before().receiver.clone(),
            rat(8, 25)
        );
        assert!(returned.balance().port.is_zero() && returned.balance().dissipated.is_zero());
        assert_eq!(returned.receipt().readings(), &[integer(4)]);
    }

    /// `Holarchy/Reception.moving_receiver_rate_of_law`, over the solved step: the returned face
    /// is the face read at the reached state, `ρ(h, x⁺) = C_S x_S⁺ + C_R x_R⁺ + o + h c`, and the
    /// source's and the receiver's motions are `C_S h F_S(x̄)` and `C_R h F_R(x̄)`, with the law's
    /// field `F(x̄) = (Ω − M) x̄ + B u` computed from the medium's own matrices at the midpoint. The
    /// step from `(2, 1)` under `u = 1` reaches `(0, 3)`.
    #[test]
    fn a_moving_receivers_face_changes_by_three_terms() {
        let omega = integer_matrix(&[&[0, -1], &[1, 0]]).unwrap();
        let resistance = integer_matrix(&[&[1, 0], &[0, 0]]).unwrap();
        let input_map = integer_matrix(&[&[1], &[1]]).unwrap();
        let law = joint(&[&[0, -1], &[1, 0]], &resistance, &input_map, None);
        let (c_source, c_receiver, chart_rate) = (integer(2), integer(-3), integer(5));
        let face = ReceiverFace::new(
            ExactRatMatrix::new(vec![vec![c_source.clone()]]).unwrap(),
            ExactRatMatrix::new(vec![vec![c_receiver.clone()]]).unwrap(),
            ints(&[1]),
            vec![chart_rate.clone()],
        )
        .unwrap();
        let (state, input) = (HolonState::new(ints(&[2, 1])), ints(&[1]));
        let returned = law.interact(&state, &input, &face, &no_receipt(2)).unwrap();
        let h = law.law().step().clone();
        assert_eq!(
            (returned.next_source(), returned.next_receiver()),
            (&ints(&[0])[..], &ints(&[3])[..])
        );
        let read = face
            .read(returned.next_source(), returned.next_receiver())
            .unwrap();
        assert_eq!(returned.face(), &[&read[0] + &h * &chart_rate]);
        // The medium's field at the midpoint, `Q = 1`.
        let mut reached = returned.next_source().to_vec();
        reached.extend_from_slice(returned.next_receiver());
        let midpoint = scale(&rat(1, 2), &add(&state.configuration, &reached));
        let drift = sub(
            &omega.apply(&midpoint).unwrap(),
            &resistance.apply(&midpoint).unwrap(),
        );
        let field = add(&drift, &input_map.apply(&input).unwrap());
        let motion = returned.face_motion();
        assert_eq!(motion.source, vec![&c_source * &h * &field[0]]);
        assert_eq!(motion.receiver, vec![&c_receiver * &h * &field[1]]);
        assert_eq!(motion.chart, vec![&h * &chart_rate]);
        assert!(!motion.source[0].is_zero() && !motion.receiver[0].is_zero());
    }

    /// `Holarchy/Reception.singular_step_refused`, `interact_ok_iff`: the active pair `ẋ = x` at step
    /// `2` has the zero step matrix `1 − (2/2)·1`, so the step is refused, as inconsistent from a
    /// nonzero state and as undetermined from rest.
    #[test]
    fn a_singular_step_is_refused() {
        let active = joint(
            &[&[0, 0], &[0, 0]],
            &zero(2, 2),
            &zero(2, 0),
            Some(ExactRatMatrix::identity(2).unwrap()),
        );
        let law = JointLaw::new(
            ReferenceHolon::new(active.law().holon().clone(), integer(2), Scheme::Midpoint)
                .unwrap(),
            1,
        )
        .unwrap();
        let interact = |state: &[i64]| {
            law.interact(
                &HolonState::new(ints(state)),
                &[],
                &ReceiverFace::receiver_state(1, 1).unwrap(),
                &no_receipt(2),
            )
        };
        assert_eq!(interact(&[1, 0]), Err(HolonError::Inconsistent));
        assert_eq!(
            interact(&[0, 0]),
            Err(HolonError::NotUniquelySolvable { nullity: 2 })
        );
    }

    /// `Holarchy/Reception.unresolved_fibre_is_plural`: a face reading one of two receiver
    /// coordinates leaves the other unresolved.
    #[test]
    fn a_face_reading_one_coordinate_leaves_the_fibre_plural() {
        let port_holon = PortHolon::medium(
            &integer_matrix(&[&[0, -1, 0], &[1, 0, 0], &[0, 0, 0]]).unwrap(),
            &zero(3, 3),
            SymmetricForm::from_diagonal(vec![integer(1); 3]),
            &zero(3, 0),
            false,
        )
        .unwrap();
        let law = JointLaw::new(
            ReferenceHolon::new(
                Holon::new(port_holon).unwrap(),
                integer(1),
                Scheme::Midpoint,
            )
            .unwrap(),
            1,
        )
        .unwrap();
        let face = ReceiverFace::new(
            zero(1, 1),
            integer_matrix(&[&[1, 0]]).unwrap(),
            ints(&[0]),
            ints(&[0]),
        )
        .unwrap();
        let returned = law
            .interact(
                &HolonState::new(ints(&[1, 0, 0])),
                &[],
                &face,
                &no_receipt(3),
            )
            .unwrap();
        assert_eq!(returned.unresolved().directions, vec![ints(&[0, 1])]);
    }
}
