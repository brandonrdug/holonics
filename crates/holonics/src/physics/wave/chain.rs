//! Propagation: the telegrapher's constitution on LC cells over a supplied incidence.

use num_traits::{One, Signed, Zero};

use crate::holon::{Holon, HolonError, PortHolon};
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::matrix;
use crate::ratio::{Rat, integer};

use super::{WaveError, check_coefficients, half, square};

/// [definition] **A junction** of the supplied incidence, oriented from one node to another.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Junction {
    pub from: usize,
    pub to: usize,
}

/// [definition] **The supplied operator**: nodes and oriented junctions. Its incidence `D` has
/// `D e from = −1`, `D e to = +1` (Lean `Physics/Wave/Energy.grad`, `div`). Its boundary is its
/// own: a node with one junction is an open end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Incidence {
    nodes: usize,
    junctions: Vec<Junction>,
}

impl Incidence {
    /// An incidence, refused at the first junction that leaves the nodes or returns to its own.
    pub fn new(nodes: usize, junctions: Vec<Junction>) -> Result<Self, WaveError> {
        for (junction, ends) in junctions.iter().enumerate() {
            for node in [ends.from, ends.to] {
                if node >= nodes {
                    return Err(WaveError::NodeOutside {
                        junction,
                        node,
                        nodes,
                    });
                }
            }
            if ends.from == ends.to {
                return Err(WaveError::Loop { junction });
            }
        }
        Ok(Self { nodes, junctions })
    }

    /// **The open chain** of `nodes` nodes: junction `e` runs from node `e` to node `e + 1` (Lean
    /// `Physics/Wave/Energy.chainIncidence`).
    pub fn open_chain(nodes: usize) -> Result<Self, WaveError> {
        if nodes < 2 {
            return Err(WaveError::TooFewNodes {
                what: "an open chain",
                least: 2,
                found: nodes,
            });
        }
        Self::new(
            nodes,
            (0..nodes - 1)
                .map(|e| Junction { from: e, to: e + 1 })
                .collect(),
        )
    }

    /// **The ring** of `nodes` nodes: the open chain closed by the junction `nodes − 1 → 0`.
    pub fn ring(nodes: usize) -> Result<Self, WaveError> {
        if nodes < 3 {
            return Err(WaveError::TooFewNodes {
                what: "a ring",
                least: 3,
                found: nodes,
            });
        }
        Self::new(
            nodes,
            (0..nodes)
                .map(|e| Junction {
                    from: e,
                    to: (e + 1) % nodes,
                })
                .collect(),
        )
    }

    pub fn nodes(&self) -> usize {
        self.nodes
    }

    pub fn junctions(&self) -> &[Junction] {
        &self.junctions
    }

    /// **The drop along each junction**, `D V`: `V(to) − V(from)`.
    pub fn grad(&self, voltage: &[Rat]) -> Result<Vec<Rat>, WaveError> {
        check_len("node voltages", self.nodes, voltage.len())?;
        Ok(self
            .junctions
            .iter()
            .map(|ends| &voltage[ends.to] - &voltage[ends.from])
            .collect())
    }

    /// **The net inflow at each node**, `Dᵀ I`: currents arriving minus currents leaving.
    pub fn div(&self, current: &[Rat]) -> Result<Vec<Rat>, WaveError> {
        check_len("junction currents", self.junctions.len(), current.len())?;
        let mut inflow = vec![Rat::zero(); self.nodes];
        for (ends, value) in self.junctions.iter().zip(current) {
            inflow[ends.to] += value;
            inflow[ends.from] -= value;
        }
        Ok(inflow)
    }
}

fn check_len(what: &'static str, expected: usize, found: usize) -> Result<(), WaveError> {
    if expected == found {
        Ok(())
    } else {
        Err(WaveError::Shape {
            what,
            expected,
            found,
        })
    }
}

/// [definition] **The constitution of the LC cells**: node capacitance `C > 0` (storage, `εΔx`),
/// node leakage `G ≥ 0` (dissipation, `σΔx`), junction inductance `L > 0` (flow inertia, `μΔx`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WaveMaterial {
    capacitance: Vec<Rat>,
    leakage: Vec<Rat>,
    inductance: Vec<Rat>,
}

impl WaveMaterial {
    /// A material, refused at the first coefficient outside its admitted sign.
    pub fn new(
        capacitance: Vec<Rat>,
        leakage: Vec<Rat>,
        inductance: Vec<Rat>,
    ) -> Result<Self, WaveError> {
        check_len("node leakages", capacitance.len(), leakage.len())?;
        check_coefficients("capacitance", &capacitance, true)?;
        check_coefficients("leakage", &leakage, false)?;
        check_coefficients("inductance", &inductance, true)?;
        Ok(Self {
            capacitance,
            leakage,
            inductance,
        })
    }

    /// One capacitance, leakage and inductance throughout an incidence.
    pub fn uniform(
        incidence: &Incidence,
        capacitance: &Rat,
        leakage: &Rat,
        inductance: &Rat,
    ) -> Result<Self, WaveError> {
        Self::new(
            vec![capacitance.clone(); incidence.nodes()],
            vec![leakage.clone(); incidence.nodes()],
            vec![inductance.clone(); incidence.junctions().len()],
        )
    }

    pub fn capacitance(&self) -> &[Rat] {
        &self.capacitance
    }

    pub fn leakage(&self) -> &[Rat] {
        &self.leakage
    }

    pub fn inductance(&self) -> &[Rat] {
        &self.inductance
    }
}

/// [definition] **A state at a whole tick**: node voltages `V` and the junction currents `I` of
/// the previous half tick. No event history is kept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WaveState {
    voltage: Vec<Rat>,
    current: Vec<Rat>,
}

impl WaveState {
    pub fn new(voltage: Vec<Rat>, current: Vec<Rat>) -> Self {
        Self { voltage, current }
    }

    /// The state at rest on an incidence.
    pub fn rest(incidence: &Incidence) -> Self {
        Self {
            voltage: vec![Rat::zero(); incidence.nodes()],
            current: vec![Rat::zero(); incidence.junctions().len()],
        }
    }

    pub fn voltage(&self) -> &[Rat] {
        &self.voltage
    }

    pub fn current(&self) -> &[Rat] {
        &self.current
    }

    /// The change between two states, node by node and junction by junction.
    pub fn difference(&self, other: &Self) -> Self {
        Self {
            voltage: self
                .voltage
                .iter()
                .zip(&other.voltage)
                .map(|(a, b)| a - b)
                .collect(),
            current: self
                .current
                .iter()
                .zip(&other.current)
                .map(|(a, b)| a - b)
                .collect(),
        }
    }
}

/// [definition] **The energy balance of one tick**, every term exact:
/// `stored_change = source_power − dissipated + residual` (Lean
/// `Physics/Wave/Energy.energy_balance`, where the residual is zero).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WaveBalance {
    /// `E(V⁺; I⁺, I⁺⁺) − E(V; I, I⁺)`, the staggered energy's change.
    pub stored_change: Rat,
    /// `h Σ G V̄²`, the leakage heat at the tick's midpoint voltage `V̄ = (V + V⁺)/2`.
    pub dissipated: Rat,
    /// `h Σ s V̄`, the power the source delivers.
    pub source_power: Rat,
    /// What the other terms do not account for.
    pub residual: Rat,
}

impl WaveBalance {
    pub fn is_exact(&self) -> bool {
        self.residual.is_zero()
    }
}

/// [definition] **A propagation return**: the next state and the tick's balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Propagation {
    pub next: WaveState,
    pub balance: WaveBalance,
}

/// [definition] **A wave field**: the supplied incidence (operator and boundary), its material
/// and its clock tick.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WaveChain {
    incidence: Incidence,
    material: WaveMaterial,
    tick: Rat,
}

impl WaveChain {
    /// A field, refused when the material does not fit the incidence or the tick does not advance.
    pub fn new(incidence: Incidence, material: WaveMaterial, tick: Rat) -> Result<Self, WaveError> {
        check_len(
            "node capacitances",
            incidence.nodes(),
            material.capacitance.len(),
        )?;
        check_len(
            "junction inductances",
            incidence.junctions().len(),
            material.inductance.len(),
        )?;
        if !tick.is_positive() {
            return Err(WaveError::Tick { tick });
        }
        Ok(Self {
            incidence,
            material,
            tick,
        })
    }

    pub fn incidence(&self) -> &Incidence {
        &self.incidence
    }

    pub fn material(&self) -> &WaveMaterial {
        &self.material
    }

    pub fn tick(&self) -> &Rat {
        &self.tick
    }

    fn check_state(&self, state: &WaveState) -> Result<(), WaveError> {
        check_len("node voltages", self.incidence.nodes(), state.voltage.len())?;
        check_len(
            "junction currents",
            self.incidence.junctions().len(),
            state.current.len(),
        )
    }

    /// The junction currents half a tick on: `I⁺ = I − (h/L) D V`.
    fn advance_current(&self, state: &WaveState) -> Result<Vec<Rat>, WaveError> {
        let drop = self.incidence.grad(&state.voltage)?;
        Ok(state
            .current
            .iter()
            .zip(drop)
            .zip(&self.material.inductance)
            .map(|((current, drop), inductance)| current - &self.tick / inductance * drop)
            .collect())
    }

    /// [definition] **The staggered energy** `½ Σ C V² + ½ Σ L I⁻ I⁺` of a state, `I⁺` its current
    /// half a tick on (Lean `Physics/Wave/Energy.energy`).
    pub fn energy(&self, state: &WaveState) -> Result<Rat, WaveError> {
        self.check_state(state)?;
        let next = self.advance_current(state)?;
        let stored: Rat = state
            .voltage
            .iter()
            .zip(&self.material.capacitance)
            .map(|(voltage, capacitance)| capacitance * square(voltage))
            .sum();
        let flowing: Rat = state
            .current
            .iter()
            .zip(&next)
            .zip(&self.material.inductance)
            .map(|((before, after), inductance)| inductance * before * after)
            .sum();
        Ok(half() * (stored + flowing))
    }

    /// [proved-derived; implemented-exact] **One tick under a source** (a current into each node).
    /// The junctions advance first, `L(I⁺ − I) = −h D V`; then each node,
    /// `C(V⁺ − V) = h Dᵀ I⁺ − h G (V⁺ + V)/2 + h s`, solved locally as
    /// `V⁺ = ((2C − hG) V + 2h (Dᵀ I⁺ + s))/(2C + hG)` (Lean `Physics/Wave/Energy.Tick`,
    /// `Physics/Wave/Telegrapher.step_is_the_telegrapher`). Returns the exact balance
    /// (`energy_balance`).
    pub fn propagate(&self, state: &WaveState, source: &[Rat]) -> Result<Propagation, WaveError> {
        self.check_state(state)?;
        check_len("node sources", self.incidence.nodes(), source.len())?;
        let current = self.advance_current(state)?;
        let inflow = self.incidence.div(&current)?;
        let h = &self.tick;
        let two = integer(2);
        let voltage: Vec<Rat> = (0..self.incidence.nodes())
            .map(|i| {
                let c = &self.material.capacitance[i];
                let g = &self.material.leakage[i];
                ((&two * c - h * g) * &state.voltage[i] + &two * h * (&inflow[i] + &source[i]))
                    / (&two * c + h * g)
            })
            .collect();
        let next = WaveState { voltage, current };
        let midpoint: Vec<Rat> = state
            .voltage
            .iter()
            .zip(&next.voltage)
            .map(|(before, after)| half() * (before + after))
            .collect();
        let dissipated: Rat = h * midpoint
            .iter()
            .zip(&self.material.leakage)
            .map(|(voltage, leakage)| leakage * square(voltage))
            .sum::<Rat>();
        let source_power: Rat = h * midpoint
            .iter()
            .zip(source)
            .map(|(voltage, source)| source * voltage)
            .sum::<Rat>();
        let stored_change = self.energy(&next)? - self.energy(state)?;
        let residual = &stored_change - (&source_power - &dissipated);
        Ok(Propagation {
            next,
            balance: WaveBalance {
                stored_change,
                dissipated,
                source_power,
                residual,
            },
        })
    }

    /// `ticks` silent ticks from `state`.
    pub fn run(&self, state: &WaveState, ticks: usize) -> Result<WaveState, WaveError> {
        let silent = vec![Rat::zero(); self.incidence.nodes()];
        let mut current = state.clone();
        for _ in 0..ticks {
            current = self.propagate(&current, &silent)?.next;
        }
        Ok(current)
    }

    /// [proved-derived; implemented-exact] **The Courant bound of the field**: the least `β` the
    /// row certificate gives, `β = max_i (Σ_(e∋i) 2/L_e)/C_i`, so that `Σ (DV)²/L ≤ β Σ C V²`
    /// (Lean `Physics/Wave/Energy.operator_bound_of_rows`; every junction row has two unit
    /// entries). For the uniform open chain it is `4/(LC)` (`chain_grad_bound`).
    pub fn courant_bound(&self) -> Rat {
        let mut row = vec![Rat::zero(); self.incidence.nodes()];
        for (ends, inductance) in self
            .incidence
            .junctions()
            .iter()
            .zip(&self.material.inductance)
        {
            let weight = integer(2) / inductance;
            row[ends.from] += &weight;
            row[ends.to] += &weight;
        }
        row.iter()
            .zip(&self.material.capacitance)
            .map(|(row, capacitance)| row / capacitance)
            .fold(
                Rat::zero(),
                |best, value| if value > best { value } else { best },
            )
    }

    /// Whether the clock satisfies the Courant condition `h² β ≤ 4`: the stability (CFL) statement
    /// that the staggered energy is bounded below ([`Self::energy_floor`]). It is not a proof that
    /// the physical cone lies inside the lattice cone.
    pub fn satisfies_courant(&self) -> bool {
        square(&self.tick) * self.courant_bound() <= integer(4)
    }

    /// [proved-derived; implemented-exact] **The energy floor**
    /// `½(1 − h²β/4) Σ C V² + ⅛ Σ (2L I − h D V)²/L`, a lower bound on the staggered energy for
    /// every state (Lean `energy_lower_bound`): the staggered flow term is
    /// `L I I⁺ = (2L I − h DV)²/(4L) − h²(DV)²/(4L)`, and the row certificate bounds the last part.
    /// Under the strict Courant condition `h²β < 4` both parts are nonnegative and vanish only at
    /// `V = 0`, `I = 0`, so the staggered energy is a norm on the state `(V, I)` (Lean
    /// `energy_definite`, `chain_energy_definite`).
    pub fn energy_floor(&self, state: &WaveState) -> Result<Rat, WaveError> {
        self.check_state(state)?;
        let stored: Rat = state
            .voltage
            .iter()
            .zip(&self.material.capacitance)
            .map(|(voltage, capacitance)| capacitance * square(voltage))
            .sum();
        let drop = self.incidence.grad(&state.voltage)?;
        let flowing: Rat = state
            .current
            .iter()
            .zip(&drop)
            .zip(&self.material.inductance)
            .map(|((current, drop), inductance)| {
                square(&(integer(2) * inductance * current - &self.tick * drop)) / inductance
            })
            .sum();
        Ok(
            half() * (Rat::one() - square(&self.tick) * self.courant_bound() / integer(4)) * stored
                + flowing / integer(8),
        )
    }

    /// [definition] **The field as a Holon** (Lean `Holon/Conformance.mediumHolon`): the
    /// port-Hamiltonian medium on the charges and fluxes `q = (C V, L I)`
    /// ([`Self::configuration`]), with storage `Q = diag(1/C, 1/L)` (so the storage effort is
    /// `(V, I)`), the skew interconnection `Ω = [[0, Dᵀ], [−D, 0]]` of the supplied incidence, the
    /// resistive relation `diag(G, 0)` (the leakage) and one external port per node carrying its
    /// source current. Its flow is the telegrapher's law `C V̇ = Dᵀ I − G V + s`, `L İ = −D V`, and
    /// its storage energy is `½ Σ C V² + ½ Σ L I²`.
    ///
    /// [definition; agent-inferred] [`Self::propagate`] is the staggered (leapfrog) integrator of
    /// this Holon, a different integrator from the reference law's implicit midpoint
    /// ([`crate::holon::law::ReferenceHolon`]): its exact balance is in the **staggered** energy
    /// `½ Σ C V² + ½ Σ L I⁻ I⁺` ([`Self::energy`]), while the midpoint's is in the storage energy.
    pub fn holon(&self) -> Result<Holon, WaveError> {
        let nodes = self.incidence.nodes();
        let junctions = self.incidence.junctions();
        let extent = nodes + junctions.len();
        // `D e i`: `+1` at the junction's `to`, `−1` at its `from`.
        let incidence = |e: usize, i: usize| {
            let ends = &junctions[e];
            if i == ends.to {
                Rat::one()
            } else if i == ends.from {
                -Rat::one()
            } else {
                Rat::zero()
            }
        };
        let omega = matrix(extent, extent, |row, column| {
            match (row < nodes, column < nodes) {
                (true, false) => incidence(column - nodes, row),
                (false, true) => -incidence(row - nodes, column),
                _ => Rat::zero(),
            }
        })
        .map_err(HolonError::from)?;
        let leakage = matrix(extent, extent, |row, column| {
            if row == column && row < nodes {
                self.material.leakage[row].clone()
            } else {
                Rat::zero()
            }
        })
        .map_err(HolonError::from)?;
        let compliance: Vec<Rat> = self
            .material
            .capacitance
            .iter()
            .chain(&self.material.inductance)
            .map(Rat::recip)
            .collect();
        let storage = SymmetricForm::from_rows(
            (0..extent)
                .map(|row| {
                    (0..extent)
                        .map(|column| {
                            if row == column {
                                compliance[row].clone()
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .map_err(HolonError::from)?;
        let sources = matrix(extent, nodes, |row, column| {
            if row == column {
                Rat::one()
            } else {
                Rat::zero()
            }
        })
        .map_err(HolonError::from)?;
        Ok(Holon::new(PortHolon::medium(
            &omega, &leakage, storage, &sources, false,
        )?)?)
    }

    /// The state in the Holon's storage coordinates: the node charges `C V` and junction fluxes
    /// `L I` ([`Self::holon`]).
    pub fn configuration(&self, state: &WaveState) -> Result<Vec<Rat>, WaveError> {
        self.check_state(state)?;
        Ok(state
            .voltage
            .iter()
            .zip(&self.material.capacitance)
            .map(|(voltage, capacitance)| capacitance * voltage)
            .chain(
                state
                    .current
                    .iter()
                    .zip(&self.material.inductance)
                    .map(|(current, inductance)| inductance * current),
            )
            .collect())
    }

    /// [definition] **The front factor** of a junction toward the node it reaches:
    /// `gain · coupling = 2h/(2C + hG) · h/L` (Lean `Physics/Wave/Telegrapher.frontFactor`).
    pub fn front_factor(&self, junction: usize, reached: usize) -> Result<Rat, WaveError> {
        let ends = self
            .incidence
            .junctions()
            .get(junction)
            .ok_or(WaveError::Shape {
                what: "junction index",
                expected: self.incidence.junctions().len(),
                found: junction,
            })?;
        if reached != ends.from && reached != ends.to {
            return Err(WaveError::NodeOutside {
                junction,
                node: reached,
                nodes: self.incidence.nodes(),
            });
        }
        let h = &self.tick;
        let c = &self.material.capacitance[reached];
        let g = &self.material.leakage[reached];
        Ok(integer(2) * h / (integer(2) * c + h * g) * (h / &self.material.inductance[junction]))
    }

    /// [definition] **Stationary under a constant source**: one tick returns the state (Lean
    /// `Physics/Wave/Radiation.Stationary`); it then emits nothing, by construction
    /// (`stationary_emits_nothing`).
    pub fn is_stationary(&self, state: &WaveState, source: &[Rat]) -> Result<bool, WaveError> {
        Ok(self.propagate(state, source)?.next == *state)
    }
}

/// [definition] **The damping ratio of a front per tick**, `2C/(2C + hG)`: the leakage multiplies
/// the lossless front by it and never moves the cone (Lean
/// `Physics/Wave/Telegrapher.frontFactor_eq_damping_mul_lossless`, `damping_eq_one_iff`).
pub fn damping(capacitance: &Rat, leakage: &Rat, tick: &Rat) -> Rat {
    integer(2) * capacitance / (integer(2) * capacitance + tick * leakage)
}
