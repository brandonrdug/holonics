//! **Element relations `𝓔`: the constitution.**
//!
//! [definition] Storage, resistive, source, active and pump relations on the port kinds
//! (`Holon/Element.lean::Ports`, `Holon/Element.lean::PortHolon`). Quadratic storage is
//! `E = ½⟨x, Qx⟩` (`Holon/Element.lean::storageEnergy`) with effort `Qx` and flow `−ẋ`; resistance
//! is `e_R = −R f_R`; external (source) ports are free and return their power; an active relation
//! `e_A = L f_A` enters with its declared power `⟨f_A, L f_A⟩`; a pump is a storage schedule
//! `Q(τ)` on a clock, whose change is deposition work (`Holon/Element.lean::PortHolon.energy_balance`,
//! `Holon/Conformance.lean::lc_pump_work`).
//!
//! [definition] **Passivity is certified, never assumed** (`Holon/Element.lean::PortHolon.passive`):
//! a resistive relation is admitted only when `⟨f, R f⟩ ≥ 0` for every `f`, which is decided exactly
//! as `n₋(sym R) = 0` by Sylvester inertia; an active relation is passive when
//! `⟨e, L e⟩ ≤ 0`, decided as `n₊(sym L) = 0` (`Holon/Deposition.lean::quad_symPart`). The passive
//! projection of an active relation is [`crate::deposition::project_passive`].
//!
//! | Lean | Rust |
//! |---|---|
//! | `Ports`, `assemble`, `power_assemble` | [`crate::holon::PortCounts`], [`crate::holon::PortHolon::assemble`] |
//! | `storageEnergy` | [`storage_energy`] |
//! | `PortHolon.passive` | [`ResistiveRelation::new`] |
//! | `PortHolon.energy_balance`, `energy_balance_const` | [`crate::law::EnergyBalance`] |

use crate::geometry::Rat;
use serde::Serialize;

use crate::exact_linear::ExactRatMatrix;
use crate::generator::Clock;
use crate::holon::HolonError;
use crate::inertia::{Inertia, SymmetricForm, inertia};
use crate::scalar::{dot, form_matrix, quad, rat, symmetric_part};

/// `½⟨x, Qx⟩` (`Holon/Element.lean::storageEnergy`).
pub fn storage_energy(storage: &SymmetricForm, x: &[Rat]) -> Result<Rat, HolonError> {
    if x.len() != storage.extent() {
        return Err(HolonError::Shape {
            what: "stored configuration",
            expected: storage.extent(),
            found: x.len(),
        });
    }
    Ok(rat(1, 2) * quad(&form_matrix(storage), x)?)
}

/// The storage effort `Qx`.
pub fn storage_effort(storage: &SymmetricForm, x: &[Rat]) -> Result<Vec<Rat>, HolonError> {
    Ok(form_matrix(storage).apply(x)?)
}

/// [definition] **A certified resistive relation** `e_R = −R f_R` with `⟨f, R f⟩ ≥ 0`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResistiveRelation {
    resistance: ExactRatMatrix,
    inertia: Inertia,
}

impl ResistiveRelation {
    /// Admit `R` when its symmetric part has no negative direction; otherwise refuse with the
    /// inertia that exhibits the active direction.
    pub fn new(resistance: ExactRatMatrix) -> Result<Self, HolonError> {
        let reading = inertia(&symmetric_part(&resistance)?);
        if reading.negative > 0 {
            return Err(HolonError::NotPassive { inertia: reading });
        }
        Ok(Self {
            resistance,
            inertia: reading,
        })
    }

    pub fn resistance(&self) -> &ExactRatMatrix {
        &self.resistance
    }

    pub fn inertia(&self) -> Inertia {
        self.inertia
    }

    /// The dissipation `⟨f, R f⟩ ≥ 0`.
    pub fn dissipation(&self, flow: &[Rat]) -> Result<Rat, HolonError> {
        Ok(quad(&self.resistance, flow)?)
    }
}

/// [definition] **An active relation** `e_A = L f_A` whose power `⟨f_A, L f_A⟩` is declared, with
/// the inertia of its symmetric part.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ActiveRelation {
    relation: ExactRatMatrix,
    inertia: Inertia,
}

impl ActiveRelation {
    pub fn new(relation: ExactRatMatrix) -> Result<Self, HolonError> {
        let reading = inertia(&symmetric_part(&relation)?);
        Ok(Self {
            relation,
            inertia: reading,
        })
    }

    pub fn relation(&self) -> &ExactRatMatrix {
        &self.relation
    }

    /// The inertia of `sym L`.
    pub fn inertia(&self) -> Inertia {
        self.inertia
    }

    /// Passive: `⟨e, L e⟩ ≤ 0` for every `e`, i.e. `n₊(sym L) = 0`.
    pub fn is_passive(&self) -> bool {
        self.inertia.positive == 0
    }

    /// The declared power `⟨f, L f⟩`.
    pub fn power(&self, flow: &[Rat]) -> Result<Rat, HolonError> {
        Ok(quad(&self.relation, flow)?)
    }
}

/// [definition] **A pump schedule** `Q(τ)`: storage forms of one extent, read periodically by
/// commit index.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PumpSchedule {
    forms: Vec<SymmetricForm>,
}

impl PumpSchedule {
    pub fn new(forms: Vec<SymmetricForm>) -> Result<Self, HolonError> {
        let Some(first) = forms.first() else {
            return Err(HolonError::Shape {
                what: "pump schedule (at least one storage form)",
                expected: 1,
                found: 0,
            });
        };
        let extent = first.extent();
        if let Some(bad) = forms.iter().find(|form| form.extent() != extent) {
            return Err(HolonError::Shape {
                what: "pump storage extent",
                expected: extent,
                found: bad.extent(),
            });
        }
        Ok(Self { forms })
    }

    pub fn period(&self) -> usize {
        self.forms.len()
    }

    pub fn extent(&self) -> usize {
        self.forms[0].extent()
    }

    /// The storage at commit `k` (periodic).
    pub fn storage_at(&self, commit: u64) -> &SymmetricForm {
        let period = self.forms.len() as u64;
        &self.forms[(commit % period) as usize]
    }
}

/// [definition] **A pump**: a storage schedule on its own clock.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pump {
    pub schedule: PumpSchedule,
    pub clock: Clock,
}

/// [definition] **The element relations** of a Holon, each on its own port kind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ElementRelation {
    /// Quadratic storage `½⟨x, Qx⟩` on the storage ports.
    Storage { form: SymmetricForm },
    /// `e_R = −R f_R`, certified passive.
    Resistive(ResistiveRelation),
    /// Free external ports; their power is what the balance returns.
    Source { ports: usize },
    /// `e_A = L f_A` with its declared power.
    Active(ActiveRelation),
    /// A storage schedule on a clock.
    Pump(Pump),
}

/// The deposition work of a storage change at a fixed configuration,
/// `½⟨x, (Q' − Q) x⟩` (`Holon/Deposition.lean::deposition_work`).
pub fn deposition_work(
    before: &SymmetricForm,
    after: &SymmetricForm,
    x: &[Rat],
) -> Result<Rat, HolonError> {
    let work = storage_energy(after, x)? - storage_energy(before, x)?;
    debug_assert_eq!(
        work,
        rat(1, 2)
            * dot(
                x,
                &form_matrix(after)
                    .subtract(&form_matrix(before))?
                    .apply(x)?
            )
    );
    Ok(work)
}

/// Whether a symmetric form is positive semidefinite, including the empty form (unlike
/// `Inertia::is_positive_semidefinite`, whose anti-vacuity rule refuses extent zero: an element on no
/// ports is lawfully passive).
pub fn is_positive_semidefinite(form: &SymmetricForm) -> bool {
    form.extent() == 0 || inertia(form).negative == 0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scalar::{int, integer_matrix, ints};
    use num_traits::Zero;

    #[test]
    fn an_active_resistance_is_refused_with_its_inertia() {
        assert!(ResistiveRelation::new(integer_matrix(&[&[2, 1], &[1, 1]]).unwrap()).is_ok());
        let refused = ResistiveRelation::new(integer_matrix(&[&[1, 0], &[0, -1]]).unwrap());
        assert!(matches!(
            refused,
            Err(HolonError::NotPassive { inertia }) if inertia.negative == 1
        ));
        // A skew part carries no power: it is admitted and dissipates only its symmetric part.
        let r = ResistiveRelation::new(integer_matrix(&[&[1, 5], &[-5, 1]]).unwrap()).unwrap();
        assert_eq!(r.dissipation(&ints(&[1, 1])).unwrap(), int(2));
        assert!(ResistiveRelation::new(ExactRatMatrix::zero(0, 0).unwrap()).is_ok());
    }

    /// The pump's storage change at `q = 1` with `Δc = 1` is the work `1/2`
    /// (`Holon/Conformance.lean::lc_pump_witness`).
    #[test]
    fn the_pump_work_at_unit_charge_is_one_half() {
        let before = SymmetricForm::from_integers(&[vec![1, 0], vec![0, 1]]).unwrap();
        let after = SymmetricForm::from_integers(&[vec![2, 0], vec![0, 1]]).unwrap();
        assert_eq!(
            deposition_work(&before, &after, &ints(&[1, 0])).unwrap(),
            rat(1, 2)
        );
        assert!(
            deposition_work(&before, &before, &ints(&[1, 0]))
                .unwrap()
                .is_zero()
        );
    }
}
