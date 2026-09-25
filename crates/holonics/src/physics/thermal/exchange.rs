//! Two thermal cells: the first law, the production rate and the tick's entropy enclosure.

use num_traits::{One, Signed, Zero};

use crate::holon::{Holon, HolonError, PortHolon};
use crate::ratio::Rat;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::matrix;

use super::port::ViscousWork;
use super::{ThermalError, nonnegative, positive};

/// [definition] **A thermal cell** under the caloric law `U = C T`: heat capacity `C > 0` and
/// internal energy `U > 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThermalCell {
    capacity: Rat,
    energy: Rat,
}

impl ThermalCell {
    pub fn new(capacity: Rat, energy: Rat) -> Result<Self, ThermalError> {
        positive("a heat capacity", &capacity)?;
        positive("an internal energy", &energy)?;
        Ok(Self { capacity, energy })
    }

    pub fn capacity(&self) -> &Rat {
        &self.capacity
    }

    pub fn energy(&self) -> &Rat {
        &self.energy
    }

    /// `T = U/C` (Lean `Physics/Thermal/Exchange.temperature`).
    pub fn temperature(&self) -> Rat {
        &self.energy / &self.capacity
    }

    /// `β = C/U`, the inverse temperature.
    pub fn inverse_temperature(&self) -> Rat {
        &self.capacity / &self.energy
    }

    /// The same cell at another internal energy.
    pub(super) fn at(&self, energy: Rat) -> Result<Self, ThermalError> {
        Self::new(self.capacity.clone(), energy)
    }
}

/// [definition] **A contact** between two cells: its conductance `κ ≥ 0` (Fourier's law).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Contact {
    conductance: Rat,
}

impl Contact {
    pub fn new(conductance: Rat) -> Result<Self, ThermalError> {
        nonnegative("a contact conductance", &conductance)?;
        Ok(Self { conductance })
    }

    pub fn conductance(&self) -> &Rat {
        &self.conductance
    }

    /// [definition] **The contact between two cells as a Holon** (Lean
    /// `Holon/Conformance.mediumHolon`, `diffusion_dissipates`): the port-Hamiltonian medium `U̇ = −M T + W` on the internal
    /// energies `U`, with storage `Q = diag(1/C₀, 1/C₁)` (so the storage effort is the temperature
    /// `T = QU`), the resistive relation `M = κ [[1, −1], [−1, 1]]` (passive, `1ᵀM = 0`), no
    /// gyration, and one external port per cell carrying its port work `W`. Its storage energy
    /// `½ Σ U²/C = ½ Σ C T²` is dissipated at `κ(T₀ − T₁)²` and its conserved first law is `Σ U`.
    ///
    /// [definition; agent-inferred] [`exchange`] is the explicit (forward Euler) integrator of this
    /// same medium: its step is `U⁺ = U + h(−M T + W)` exactly, which conserves the first law `ΣU`
    /// exactly and carries the Clausius production reading. The reference law's implicit midpoint
    /// ([`crate::holon::law::ReferenceHolon`]) is a different integrator of the same Holon, whose
    /// exact balance is in the storage energy `½ Σ C T²`.
    pub fn holon(&self, cells: &[ThermalCell; 2]) -> Result<Holon, ThermalError> {
        let kappa = &self.conductance;
        let laplacian = matrix(2, 2, |i, j| {
            if i == j {
                kappa.clone()
            } else {
                -kappa.clone()
            }
        })
        .map_err(HolonError::from)?;
        let storage = SymmetricForm::from_rows(vec![
            vec![cells[0].capacity().recip(), Rat::zero()],
            vec![Rat::zero(), cells[1].capacity().recip()],
        ])
        .map_err(HolonError::from)?;
        let omega = matrix(2, 2, |_, _| Rat::zero()).map_err(HolonError::from)?;
        let ports = matrix(2, 2, |i, j| if i == j { Rat::one() } else { Rat::zero() })
            .map_err(HolonError::from)?;
        Ok(Holon::new(PortHolon::medium(
            &omega, &laplacian, storage, &ports, false,
        )?)?)
    }
}

/// [definition] **The entropy of a tick, enclosed**: the change `ΔS = Σ C log(U'/U)` lies in
/// `[lower, upper]`, both exact rationals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EntropyEnclosure {
    pub lower: Rat,
    pub upper: Rat,
}

impl EntropyEnclosure {
    /// [proved-derived; implemented-exact] **One cell's entropy over a tick**:
    /// `ΔU · C/U' ≤ C log(U'/U) ≤ ΔU · C/U` (Lean `Physics/Thermal/Exchange.cell_entropy_enclosure`).
    /// The two cells share one capacity.
    pub fn of_cell(before: &ThermalCell, after: &ThermalCell) -> Self {
        let change = after.energy() - before.energy();
        Self {
            lower: &change * after.inverse_temperature(),
            upper: change * before.inverse_temperature(),
        }
    }

    /// The enclosure of the sum of two changes.
    pub fn plus(&self, other: &Self) -> Self {
        Self {
            lower: &self.lower + &other.lower,
            upper: &self.upper + &other.upper,
        }
    }

    /// Whether the enclosure certifies `ΔS ≥ 0`.
    pub fn is_certified_nonnegative(&self) -> bool {
        !self.lower.is_negative()
    }
}

/// [definition] **An exchange return**: the heat, both cells after the tick, the first law's
/// residual, the production rate and the entropy of the tick.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExchangeReturn {
    /// `q = hκ(T₀ − T₁)`, carried from cell 0 to cell 1 over the tick.
    pub heat: Rat,
    /// The cells after the tick: contact heat, then the ports' work.
    pub next: [ThermalCell; 2],
    /// `(ΔU₀ + ΔU₁) − h(W₀ + W₁)`: zero by construction of the update (Lean `first_law`).
    pub first_law_residual: Rat,
    /// `κ(T₀ − T₁)²/(T₀T₁) + W₀/T₀ + W₁/T₁` at the start of the tick (Lean `productionRate_eq`,
    /// `hasDerivAt_entropy`).
    pub production_rate: Rat,
    /// The contact's share of the tick's entropy (Lean `exchange_entropy_enclosure`).
    pub contact_entropy: EntropyEnclosure,
    /// Each port's share of the tick's entropy (Lean `ViscousPort.port_entropy_enclosure`).
    pub port_entropy: [EntropyEnclosure; 2],
}

impl ExchangeReturn {
    /// The whole tick's entropy enclosure.
    pub fn entropy(&self) -> EntropyEnclosure {
        self.contact_entropy
            .plus(&self.port_entropy[0])
            .plus(&self.port_entropy[1])
    }
}

/// [proved-derived; implemented-exact] **One tick of two cells through a contact, with the work of
/// their ports.** The contact carries `q = hκ(T₀ − T₁)` (Lean `Physics/Thermal/Exchange.heat`),
/// then each port adds `hW` (Lean `Physics/Thermal/ViscousPort`). Refused when the tick does not
/// advance or overshoots, `hκ(1/C₀ + 1/C₁) > 1` (Lean `overshoot_destroys_entropy`); under the
/// tick condition every lower Clausius reading is nonnegative (`exchange_entropy_nonneg`,
/// `port_entropy_nonneg`).
pub fn exchange(
    cells: &[ThermalCell; 2],
    contact: &Contact,
    tick: &Rat,
    work: &[ViscousWork; 2],
) -> Result<ExchangeReturn, ThermalError> {
    positive("a tick", tick)?;
    let factor =
        tick * contact.conductance() * (cells[0].capacity().recip() + cells[1].capacity().recip());
    if factor > Rat::one() {
        return Err(ThermalError::Overshoot { factor });
    }
    let (t0, t1) = (cells[0].temperature(), cells[1].temperature());
    let heat = tick * contact.conductance() * (&t0 - &t1);
    let contacted = [
        cells[0].at(cells[0].energy() - &heat)?,
        cells[1].at(cells[1].energy() + &heat)?,
    ];
    let mut next = contacted.clone();
    let mut port_entropy = [
        EntropyEnclosure {
            lower: Rat::zero(),
            upper: Rat::zero(),
        },
        EntropyEnclosure {
            lower: Rat::zero(),
            upper: Rat::zero(),
        },
    ];
    for side in 0..2 {
        let port = work[side].receive(&contacted[side], tick)?;
        port_entropy[side] = port.entropy;
        next[side] = port.next;
    }
    let first_law_residual = (next[0].energy() - cells[0].energy())
        + (next[1].energy() - cells[1].energy())
        - tick * (work[0].power() + work[1].power());
    let difference = &t0 - &t1;
    let production_rate = contact.conductance() * &difference * &difference / (&t0 * &t1)
        + work[0].production_rate(&cells[0])
        + work[1].production_rate(&cells[1]);
    let contact_entropy = EntropyEnclosure::of_cell(&cells[0], &contacted[0])
        .plus(&EntropyEnclosure::of_cell(&cells[1], &contacted[1]));
    Ok(ExchangeReturn {
        heat,
        next,
        first_law_residual,
        production_rate,
        contact_entropy,
        port_entropy,
    })
}
