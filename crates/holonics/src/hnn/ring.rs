//! **The ring's parametron: its mode tick, its storage form, its pump and sheets, its clock, and its
//! junction's reference change** (campaign 2, Lean `HNN/Ring`).
//!
//! [definition] A ring is a complex parametron: it stores, oscillates and locks. Campaign 1 gave each
//! ring its rotor clock and its element (the Cayley step of the storage wave, `hnn::propagation`);
//! campaign 2 gives it its **mode storage** `Q = diag(K, C)` on the pair `(u, w)` of node flux and
//! node velocity in the ring's realified chart (node `k`'s complex amplitude is `u_(2k) + i u_(2k+1)`),
//! from the ring's [`crate::holon::parametron::Parametron`] (`C = BᵀW_C B`, `K = BᵀW_K B`, each on the
//! real and the imaginary coordinate), a dissipation `D` and its pump. It is a **resonator** at the
//! ring's storage port: at every tick the storage wave `β = b_r` the junction sends into the ring's
//! storage drives it through a port of the ring's storage admittance `Y_r`:
//!
//! ```text
//! pump       K_t = K + ⊕_k −2p [[cos ψ_t, sin ψ_t], [sin ψ_t, −cos ψ_t]]      e^(iψ_t) = a² s^t
//! solve      M_t ω = 2C w + h β − h K_t u ,   M_t = 2C + (h/Y) I + h D + (h²/2) K_t
//! state      u′ = u + h ω ,   w′ = 2ω − w                                  (split on 2^(−L_w)ℤ)
//! balance    E_(K_t)(û′, ŵ′) − E_(K_(t−1))(u, w) = pump + port − dissipation + chart + split
//!            pump = ½⟨u, (K_t − K_(t−1)) u⟩ ,   port = (hY/4)(|β|² − |β − (2/Y)ω|²)
//!            dissipation = h⟨ω, D ω⟩ ,   chart = ⟨ω, M_t ω − r⟩ ,   split = E(û′, ŵ′) − E(u′, w′)
//! ```
//!
//! [proved-derived; implemented-exact] **Its laws** (Lean `HNN/Ring`). Closed, lossless and unpumped,
//! the tick keeps its storage form, sign included: `UᵀQU = Q` (`ring_tick_conserves_mode_energy`),
//! and the descriptor form solved here conserves `E_Q` without `C⁻¹`
//! (`ring_descriptor_tick_conserves`). Its operator is positive definite with its port and
//! `C, D, K ⪰ 0` (`ring_cayley_denominator_nonsingular`); a pumped `K_t` may be indefinite, so each
//! pump phase is certified by its signed form `2C + hD + (h²/2) K_t ⪰ 0`, which bounds `⟨v, M_t v⟩`
//! below by `(h/Y)|v|²` (the contact's certificate, `HNN/Contact.contact_boost_solve_or_singular_direction`),
//! and refused otherwise ([`ResonatorMaterial::certify`]). The executed tick closes exactly with
//! every term stated (`ring_tick_executed_energy_balance`, [`ResonatorStep::closes`]). The pump reads
//! the doubled phase: invariant under the half-turn (`pump_half_turn_invariant`) and blind to the two
//! sheets of its axis `a = e^(iφ)`, `ψ = 2φ` (`pump_blind_to_sheets`); a node's **sheet** is its
//! amplitude's side of the axis, the threshold of its in-phase projection, the Ising face of the
//! locked sheets whose threshold is the perceptron (`locked_sheet_receiver_face`,
//! [`sheets`]).
//!
//! [definition; agent-inferred] **The resonator receives the storage wave; it does not load it.** The
//! word's return (`hnn::port`'s pull-back, the exact adjoint of the executed forward) does not pass
//! through the resonator in campaign 2, so the resonator stands at the ring's storage port as a
//! driven receiver: the port work it draws is stated in its own balance and enters the field's
//! whole balance as the resonator's port work (`hnn::word::FieldBalance`), and the waves, the
//! return and every campaign-1 reading are unchanged. Loading the port (the resonator's returned
//! wave `β − (2/Y) ω` fed back into the ring's storage) needs the return through the resonator; it is
//! the remaining scope (#73). A ring without a declared resonator (every campaign-1 constitution) has
//! none, and its word is campaign 1's.
//!
//! [definition; agent-inferred] **The pump's phases are finite.** The pump carrier advances by a
//! declared rational rotation per tick; the only rational rotations of finite order in the plane are
//! the quarter turns, so the pump's step is one of them ([`PumpStep`]) and a word visits at most four
//! pump phases, each with its own operator and chart. A pump of infinite order would give each tick
//! its own operator; it is not declared.
//!
//! [proved-derived; implemented-exact] **The clock** ([`RingClock`]). The ring's rotor steps `1/d` of
//! a turn per micro-step; over a passage of cells its arrivals on its section (the lift's multiples of
//! `d`) are its epoch ticks, `(r + N)/d` of them from residue `r` after `N` micro-steps
//! (`ring_crossings_are_epoch_ticks`, the owner [`crate::holon::parametron::ring_crossings`]); they
//! are the carries it sends down the carry chain.
//!
//! [proved-derived; implemented-exact] **The reference change at a junction port**
//! ([`port_scattering`]). A wave arriving at port `p` of a junction meets the rest of the junction as
//! one reference admittance `G_rest = W − G_p`: it reflects `Γ = (G_p − G_rest)/(G_p + G_rest)` and
//! transmits the power fraction `T = 4G_p G_rest/(G_p + G_rest)²` into the other ports, `Γ² + T = 1`
//! (`two_port_reference_balance`); the executed Swing returns exactly `Γ` and `1 + Γ`.
//!
//! | Lean `HNN/Ring` | Rust |
//! |---|---|
//! | `cayley_preserves_form`, `ring_generator_qSkew`, `ring_tick_conserves_mode_energy`, `ring_descriptor_tick_conserves` | [`ResonatorOperands::step`] (closed and lossless in the tests) |
//! | `ring_cayley_denominator_nonsingular`, `ring_harmonic_mode_singular` | [`ResonatorMaterial::certify`] |
//! | `ring_tick_port_balance`, `ring_tick_executed_energy_balance` | [`ResonatorStep`], [`ResonatorStep::closes`] |
//! | `two_port_reference_balance` | [`port_scattering`], [`PortScattering`] |
//! | `ring_crossings_are_epoch_ticks` | [`RingClock::over`] |
//! | `pump_half_turn_invariant`, `pump_blind_to_sheets`, `locked_sheet_receiver_face` | [`PumpDeclaration`], [`sheets`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use crate::hnn::HnnError;
use crate::hnn::chart::{ChartKey, ChartReading, ChartWords, WordLattice, carry, refine};
use crate::hnn::constitution::Lattice;
use crate::hnn::contact::symmetric;
use crate::hnn::field::{Current, Field};
use crate::holon::parametron::{Carrier, Parametron, ring_crossings, threshold_sheet};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::inertia;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::{Rat, integer};

// -------------------------------------------------------------------------------------------
// the pump

/// [definition] **The pump's step per tick**: a quarter-turn power, the rational rotations of finite
/// order (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PumpStep {
    /// The pump stands.
    Stand,
    /// A quarter turn per tick.
    Quarter,
    /// A half turn per tick.
    Half,
    /// Three quarter turns per tick.
    ThreeQuarters,
}

impl PumpStep {
    /// The pump phases a word visits: the step's order.
    pub fn order(self) -> usize {
        match self {
            Self::Stand => 1,
            Self::Half => 2,
            Self::Quarter | Self::ThreeQuarters => 4,
        }
    }

    fn quarters(self) -> u64 {
        match self {
            Self::Stand => 0,
            Self::Quarter => 1,
            Self::Half => 2,
            Self::ThreeQuarters => 3,
        }
    }
}

/// `(a + ib)(c + id)` on unit carriers.
fn compose(first: &Carrier, second: &Carrier) -> Carrier {
    Carrier::new(
        first.cos() * second.cos() - first.sin() * second.sin(),
        first.cos() * second.sin() + first.sin() * second.cos(),
    )
    .expect("the product of two unit carriers is a unit carrier")
}

/// The quarter turn `i^k`.
fn quarter_turn(k: u64) -> Carrier {
    let (cos, sin) = match k % 4 {
        0 => (1, 0),
        1 => (0, 1),
        2 => (-1, 0),
        _ => (0, -1),
    };
    Carrier::new(integer(cos), integer(sin)).expect("a quarter turn is a unit carrier")
}

/// [definition] **A ring's pump**: its strength `p ≥ 0`, its locking axis `a = e^(iφ)` (a rational
/// point of the circle, whose sheets are `φ` and `φ + π`), and its step per tick. Its carrier at tick
/// `t` is `e^(iψ_t) = a² s^t`: at `t = 0` the pump sits at twice its axis (`pump_blind_to_sheets`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpDeclaration {
    strength: Rat,
    axis: Carrier,
    step: PumpStep,
}

impl PumpDeclaration {
    pub fn new(strength: Rat, axis: Carrier, step: PumpStep) -> Result<Self, HnnError> {
        if strength.is_negative() {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a pump's strength is nonnegative",
            });
        }
        Ok(Self {
            strength,
            axis,
            step,
        })
    }

    pub fn strength(&self) -> &Rat {
        &self.strength
    }

    pub fn axis(&self) -> &Carrier {
        &self.axis
    }

    pub fn step(&self) -> PumpStep {
        self.step
    }

    /// The pump phases a word visits.
    pub fn phases(&self) -> usize {
        self.step.order()
    }

    /// **The pump carrier** `e^(iψ)` at phase `j`: `a² i^(j·k)`.
    pub fn carrier(&self, phase: usize) -> Carrier {
        let doubled = compose(&self.axis, &self.axis);
        compose(&doubled, &quarter_turn(self.step.quarters() * phase as u64))
    }

    /// **The node block** `−2p [[cos ψ, sin ψ], [sin ψ, −cos ψ]]` the pump adds to a node's `K`
    /// (Lean `HNN/Ring.pumpBlock`, read as `½ zᵀ K z`).
    pub fn block(&self, phase: usize) -> [[Rat; 2]; 2] {
        let psi = self.carrier(phase);
        let twice = integer(-2) * &self.strength;
        [
            [&twice * psi.cos(), &twice * psi.sin()],
            [&twice * psi.sin(), -(&twice * psi.cos())],
        ]
    }
}

/// **A node's sheet**: the half-turn sheet exactly when its amplitude lies on the far side of the
/// axis, `Re(z ā) < 0` (the threshold of its in-phase projection, `Objects/Parametron.sheetReading`
/// relative to the axis). A node on the axis's line reads its locked sheet back
/// (`sheetReading_binaryPhase`).
pub fn sheets(displacement: &[Rat], axis: &Carrier) -> Vec<bool> {
    displacement
        .chunks(2)
        .map(|node| {
            let in_phase =
                &node[0] * axis.cos() + node.get(1).map_or_else(Rat::zero, |y| y * axis.sin());
            threshold_sheet(&in_phase)
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the material

/// [definition] **A ring's resonator material** in `Θ`: its storage `C` on the rate, its stiffness `K`
/// on the displacement, its dissipation `D` on the rate (each symmetric on the ring's realified
/// width; `C, D ⪰ 0`), and its pump. It is declared, not learned, in campaign 2.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorMaterial {
    capacity: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    pump: Option<PumpDeclaration>,
}

impl ResonatorMaterial {
    /// A resonator from its three forms and its pump, each form checked square and symmetric on one
    /// even width, `C` and `D` positive semidefinite.
    pub fn new(
        capacity: ExactRatMatrix,
        stiffness: ExactRatMatrix,
        dissipation: ExactRatMatrix,
        pump: Option<PumpDeclaration>,
    ) -> Result<Self, HnnError> {
        let n = capacity.rows();
        for form in [&capacity, &stiffness, &dissipation] {
            if form.rows() != n || form.columns() != n {
                return Err(HnnError::Shape {
                    what: "a resonator form (the ring's realified width)",
                    expected: n,
                    found: form.rows(),
                });
            }
        }
        if !n.is_multiple_of(2) {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a resonator lives on a realified width (two coordinates per node)",
            });
        }
        for form in [&capacity, &dissipation] {
            if inertia(&symmetric(form)?).negative != 0 {
                return Err(HnnError::Resonator {
                    ring: usize::MAX,
                    what: "a resonator's storage and dissipation are positive semidefinite",
                });
            }
        }
        symmetric(&stiffness)?;
        Ok(Self {
            capacity,
            stiffness,
            dissipation,
            pump,
        })
    }

    /// **The parametron's resonator** (module header): `C = BᵀW_C B` and `K = BᵀW_K B` on the real and
    /// the imaginary coordinate of each node, the dissipation `d·I`, and the pump.
    pub fn of_parametron(
        parametron: &Parametron,
        dissipation: &Rat,
        pump: Option<PumpDeclaration>,
    ) -> Result<Self, HnnError> {
        let realify = |form: ExactRatMatrix| -> Result<ExactRatMatrix, HnnError> {
            let d = form.rows();
            Ok(ExactRatMatrix::shaped(
                2 * d,
                2 * d,
                (0..2 * d)
                    .map(|i| {
                        (0..2 * d)
                            .map(|j| {
                                if i % 2 == j % 2 {
                                    form.get(i / 2, j / 2).expect("in range").clone()
                                } else {
                                    Rat::zero()
                                }
                            })
                            .collect()
                    })
                    .collect(),
            )?)
        };
        let n = 2 * parametron.nodes();
        Self::new(
            realify(parametron.capacitance()?)?,
            realify(parametron.stiffness()?)?,
            ExactRatMatrix::identity(n)?.scaled(dissipation),
            pump,
        )
    }

    pub fn width(&self) -> usize {
        self.capacity.rows()
    }

    /// `C`, `K`, `D`.
    pub fn forms(&self) -> (&ExactRatMatrix, &ExactRatMatrix, &ExactRatMatrix) {
        (&self.capacity, &self.stiffness, &self.dissipation)
    }

    pub fn pump(&self) -> Option<&PumpDeclaration> {
        self.pump.as_ref()
    }

    /// The pump phases a word visits (one unpumped).
    pub fn phases(&self) -> usize {
        self.pump.as_ref().map_or(1, PumpDeclaration::phases)
    }

    /// **The pumped stiffness** `K_j`: `K` with the pump's node block added on every node.
    pub fn pumped_stiffness(&self, phase: usize) -> Result<ExactRatMatrix, HnnError> {
        let Some(pump) = &self.pump else {
            return Ok(self.stiffness.clone());
        };
        let block = pump.block(phase);
        let n = self.width();
        Ok(ExactRatMatrix::shaped(
            n,
            n,
            (0..n)
                .map(|i| {
                    (0..n)
                        .map(|j| {
                            let base = self.stiffness.get(i, j).expect("in range").clone();
                            if i / 2 == j / 2 {
                                base + &block[i % 2][j % 2]
                            } else {
                                base
                            }
                        })
                        .collect()
                })
                .collect(),
        )?)
    }

    /// **The resonator's certificate** at hop `h` (module header): at every pump phase the signed
    /// form `2C + hD + (h²/2) K_j` is positive semidefinite, so each phase's operator solves
    /// uniquely; refused with the first phase that is not.
    pub fn certify(&self, ring: usize, step: &Rat) -> Result<(), HnnError> {
        for phase in 0..self.phases() {
            let form = self
                .capacity
                .scaled(&integer(2))
                .add(&self.dissipation.scaled(step))?
                .add(
                    &self
                        .pumped_stiffness(phase)?
                        .scaled(&(step * step / integer(2))),
                )?;
            if inertia(&symmetric(&form)?).negative != 0 {
                return Err(HnnError::UncertifiedResonator { ring, phase });
            }
        }
        Ok(())
    }

    /// `E_Q(u, w) = ½⟨w, C w⟩ + ½⟨u, K_j u⟩` at pump phase `j`.
    pub fn energy(
        &self,
        phase: usize,
        displacement: &[Rat],
        rate: &[Rat],
    ) -> Result<Rat, HnnError> {
        let stiffness = self.pumped_stiffness(phase)?;
        Ok((dot(rate, &self.capacity.apply(rate)?)
            + dot(displacement, &stiffness.apply(displacement)?))
            / integer(2))
    }
}

// -------------------------------------------------------------------------------------------
// the operands at the cut and the tick

/// The executed solve of one pump phase's operator: the exact inverse (the law) or a certified
/// lattice chart (Decision 24) with its reading.
#[derive(Clone, Debug, PartialEq, Eq)]
enum PhaseSolve {
    Exact(ExactRatMatrix),
    Chart(ChartWords),
}

impl PhaseSolve {
    fn apply(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact(inverse) => Ok(inverse.apply(vector)?),
            Self::Chart(chart) => chart.apply(vector),
        }
    }
}

/// One pump phase's operands: its stiffness `K_j`, its operator `M_j` and its executed solve.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Phase {
    stiffness: ExactRatMatrix,
    operator: ExactRatMatrix,
    solve: PhaseSolve,
    reading: Option<ResonatorChart>,
}

/// [definition] **A resonator chart's reading**: the ring, the pump phase, the certificate
/// `‖1 − M X̂‖∞`, its target and the refinement's steps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorChart {
    pub ring: usize,
    pub phase: usize,
    pub certificate: Rat,
    pub target: Rat,
    pub steps: u32,
}

/// [definition] **A resonator's operands at a word's cut**: its material, the ring's storage
/// admittance `Y` (its port), the hop `h`, and each pump phase's operator with its executed solve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorOperands {
    ring: usize,
    material: ResonatorMaterial,
    admittance: Rat,
    step: Rat,
    phases: Vec<Phase>,
}

/// [definition] **One executed resonator tick**: the tick's pump phase, the energy before (at the
/// previous phase's stiffness) and after (the carried state at this phase's), and every term of the
/// executed balance (module header), with the carried state and the remainders it leaves.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorStep {
    pub phase: usize,
    pub before: Rat,
    pub after: Rat,
    pub pump: Rat,
    pub port: Rat,
    pub dissipation: Rat,
    pub chart: Rat,
    pub split: Rat,
    pub state: [Vec<Rat>; 2],
    pub rate: Vec<Rat>,
    remainders: ResonatorRemainders,
}

/// The resonator's carried remainders: its solved rate's and its state's.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ResonatorRemainders {
    pub rate: Vec<Rat>,
    pub state: [Vec<Rat>; 2],
}

impl ResonatorRemainders {
    fn zero(width: usize) -> Self {
        Self {
            rate: vec![Rat::zero(); width],
            state: [vec![Rat::zero(); width], vec![Rat::zero(); width]],
        }
    }

    /// Every remainder, the rate's first.
    pub fn all(&self) -> impl Iterator<Item = &Rat> {
        self.rate.iter().chain(self.state.iter().flatten())
    }
}

impl ResonatorStep {
    /// **The executed balance closes exactly** (Lean `HNN/Ring.ring_tick_executed_energy_balance`):
    /// `after − before = pump + port − dissipation + chart + split`.
    pub fn closes(&self) -> bool {
        &self.after - &self.before
            == &self.pump + &self.port - &self.dissipation + &self.chart + &self.split
    }

    /// The carried remainders this tick leaves.
    pub fn remainders(&self) -> &ResonatorRemainders {
        &self.remainders
    }
}

impl ResonatorOperands {
    /// **A ring's resonator operands at the cut**: certified at every pump phase
    /// ([`ResonatorMaterial::certify`]), each phase's operator `M_j = 2C + (h/Y)I + hD + (h²/2)K_j`
    /// solved exactly (the law) or charted on the word's lattices from a cold start.
    pub fn at_cut(
        ring: usize,
        material: &ResonatorMaterial,
        admittance: &Rat,
        step: &Rat,
        lattice: Option<&WordLattice>,
    ) -> Result<Self, HnnError> {
        if !admittance.is_positive() || !step.is_positive() {
            return Err(HnnError::NonpositiveDeclaration);
        }
        material.certify(ring, step)?;
        let (capacity, _, dissipation) = material.forms();
        let n = material.width();
        let phases = (0..material.phases())
            .map(|phase| {
                let stiffness = material.pumped_stiffness(phase)?;
                let operator = capacity
                    .scaled(&integer(2))
                    .add(&ExactRatMatrix::identity(n)?.scaled(&(step / admittance)))?
                    .add(&dissipation.scaled(step))?
                    .add(&stiffness.scaled(&(step * step / integer(2))))?;
                let (solve, reading) = match lattice {
                    None => (PhaseSolve::Exact(operator.inverse()?), None),
                    Some(lattice) => {
                        let (chart, read): (ChartWords, ChartReading) =
                            refine(ChartKey::Ring(ring), &operator, None, lattice)?;
                        (
                            PhaseSolve::Chart(chart),
                            Some(ResonatorChart {
                                ring,
                                phase,
                                certificate: read.certificate,
                                target: read.target,
                                steps: read.steps,
                            }),
                        )
                    }
                };
                Ok(Phase {
                    stiffness,
                    operator,
                    solve,
                    reading,
                })
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        Ok(Self {
            ring,
            material: material.clone(),
            admittance: admittance.clone(),
            step: step.clone(),
            phases,
        })
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    pub fn material(&self) -> &ResonatorMaterial {
        &self.material
    }

    pub fn width(&self) -> usize {
        self.material.width()
    }

    /// `Y`, the port's admittance.
    pub fn admittance(&self) -> &Rat {
        &self.admittance
    }

    /// The pump phase at word tick `t`.
    pub fn phase_at(&self, tick: usize) -> usize {
        tick % self.phases.len()
    }

    /// The operator `M_j` of pump phase `j`.
    pub fn operator(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].operator
    }

    /// The pumped stiffness `K_j`.
    pub fn stiffness(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].stiffness
    }

    /// Every chart's reading (none under the exact law).
    pub fn charts(&self) -> Vec<ResonatorChart> {
        self.phases
            .iter()
            .filter_map(|phase| phase.reading.clone())
            .collect()
    }

    fn energy_at(&self, phase: usize, displacement: &[Rat], rate: &[Rat]) -> Result<Rat, HnnError> {
        let (capacity, _, _) = self.material.forms();
        Ok((dot(rate, &capacity.apply(rate)?)
            + dot(
                displacement,
                &self.phases[phase].stiffness.apply(displacement)?,
            ))
            / integer(2))
    }

    /// **One executed resonator tick** at word tick `t` (module header): the drive `β` (the storage
    /// wave the junction sends into the ring), the state `[u, w]` and the remainders the last tick
    /// left; each image split on `lattice` (the transients', or `None` under the exact law).
    pub fn step(
        &self,
        tick: usize,
        drive: &[Rat],
        state: [&[Rat]; 2],
        remainders: &ResonatorRemainders,
        lattice: Option<&Lattice>,
    ) -> Result<ResonatorStep, HnnError> {
        let n = self.width();
        if drive.len() != n || state[0].len() != n || state[1].len() != n {
            return Err(HnnError::Shape {
                what: "a resonator's drive and state (the ring's realified width)",
                expected: n,
                found: drive.len().min(state[0].len()).min(state[1].len()),
            });
        }
        let remainders = if remainders.rate.len() == n {
            remainders.clone()
        } else {
            ResonatorRemainders::zero(n)
        };
        let phase = self.phase_at(tick);
        let previous = if tick == 0 {
            phase
        } else {
            self.phase_at(tick - 1)
        };
        let (u, w) = (state[0], state[1]);
        let h = &self.step;
        let (capacity, _, dissipation) = self.material.forms();
        let stiffness = &self.phases[phase].stiffness;
        // r = 2C w + h β − h K_j u
        let right = sub(
            &add(&scale(&integer(2), &capacity.apply(w)?), &scale(h, drive)),
            &scale(h, &stiffness.apply(u)?),
        );
        let image = self.phases[phase].solve.apply(&right)?;
        let split = |image: Vec<Rat>, remainder: &[Rat]| -> (Vec<Rat>, Vec<Rat>) {
            match lattice {
                Some(lattice) => {
                    let mut next = remainder.to_vec();
                    let carried = carry(lattice, &image, &mut next);
                    (carried, next)
                }
                None => (image, remainder.to_vec()),
            }
        };
        let (rate, rate_remainder) = split(image, &remainders.rate);
        let displacement_image = add(u, &scale(h, &rate));
        let velocity_image = sub(&scale(&integer(2), &rate), w);
        let (displacement, displacement_remainder) =
            split(displacement_image.clone(), &remainders.state[0]);
        let (velocity, velocity_remainder) = split(velocity_image.clone(), &remainders.state[1]);
        let before = self.energy_at(previous, u, w)?;
        let pump = if previous == phase {
            Rat::zero()
        } else {
            dot(
                u,
                &stiffness
                    .subtract(&self.phases[previous].stiffness)?
                    .apply(u)?,
            ) / integer(2)
        };
        let out = sub(drive, &scale(&(integer(2) / &self.admittance), &rate));
        let port = h * &self.admittance / integer(4) * (dot(drive, drive) - dot(&out, &out));
        let dissipation_work = h * dot(&rate, &dissipation.apply(&rate)?);
        let chart = dot(
            &rate,
            &sub(&self.phases[phase].operator.apply(&rate)?, &right),
        );
        let after = self.energy_at(phase, &displacement, &velocity)?;
        let split_term = &after - self.energy_at(phase, &displacement_image, &velocity_image)?;
        Ok(ResonatorStep {
            phase,
            before,
            after,
            pump,
            port,
            dissipation: dissipation_work,
            chart,
            split: split_term,
            state: [displacement, velocity],
            rate,
            remainders: ResonatorRemainders {
                rate: rate_remainder,
                state: [displacement_remainder, velocity_remainder],
            },
        })
    }
}

// -------------------------------------------------------------------------------------------
// the rotor's clock

/// [definition] **A ring's clock over a passage of cells** (Lean
/// `HNN/Ring.ring_crossings_are_epoch_ticks`): its period `d`, its residue `r` at the passage's
/// start, the micro-steps `N` it took, its arrivals on its section (the epoch ticks, `(r + N)/d`),
/// and the micro-steps at which it arrived.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingClock {
    pub ring: usize,
    pub period: u64,
    pub residue: u64,
    pub micro_steps: BigUint,
    pub crossings: BigUint,
    pub ticks: Vec<usize>,
}

impl RingClock {
    /// **Every ring's clock over a passage of cells** from a lift point: the lift stepped cell by
    /// cell (`Field::selective_step`, carries included), each micro-step that lands on the ring's
    /// section counted as an epoch tick. The count equals the owner's `ring_crossings(d, r, N)` and
    /// the ring's winding difference, which [`RingClock::agrees`] checks.
    pub fn over(field: &Field, start: &Current, cells: &[usize]) -> Result<Vec<Self>, HnnError> {
        let mut current = start.clone();
        let mut clocks: Vec<Self> = (0..field.rings().len())
            .map(|ring| {
                let period = field.ring(ring).period();
                Ok(Self {
                    ring,
                    period,
                    residue: current.phase(field, ring)?,
                    micro_steps: BigUint::zero(),
                    crossings: BigUint::zero(),
                    ticks: Vec::new(),
                })
            })
            .collect::<Result<_, HnnError>>()?;
        let mut micro: Vec<usize> = vec![0; field.rings().len()];
        for &cell in cells {
            let before: Vec<BigInt> = current.lift().to_vec();
            let stepped = current.step(field, cell)?;
            for (ring, clock) in clocks.iter_mut().enumerate() {
                let taken = u64::from(stepped.ticks[ring]);
                let d = BigInt::from(clock.period);
                for k in 1..=taken {
                    let position = &before[ring] + BigInt::from(k);
                    micro[ring] += 1;
                    if (&position % &d).is_zero() {
                        clock.crossings += BigUint::one();
                        clock.ticks.push(micro[ring]);
                    }
                }
                clock.micro_steps += BigUint::from(taken);
            }
        }
        Ok(clocks)
    }

    /// **The count is the owner's**: the arrivals equal `ring_crossings(d, r, N)` (Lean
    /// `ringCrossings_eq`), and every arrival is a micro-step inside the passage.
    pub fn agrees(&self) -> Result<bool, HnnError> {
        let owner = ring_crossings(
            &BigUint::from(self.period),
            &BigUint::from(self.residue),
            &self.micro_steps,
        )?;
        let inside = self
            .ticks
            .iter()
            .all(|tick| BigUint::from(*tick) <= self.micro_steps);
        Ok(owner == self.crossings && inside && BigUint::from(self.ticks.len()) == self.crossings)
    }
}

// -------------------------------------------------------------------------------------------
// the reference change at a junction port

/// [definition] **A junction port's reference change** (Lean `two_port_reference_balance`): the
/// reflection `Γ` and the power transmission fraction `T` of a wave arriving at the port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortScattering {
    pub reflection: Rat,
    pub transmission: Rat,
}

impl PortScattering {
    /// `Γ² + T = 1`.
    pub fn balances(&self) -> bool {
        &self.reflection * &self.reflection + &self.transmission == Rat::one()
    }
}

/// **The reference change at port `port` of a junction** (module header): port 0 is the ring's
/// storage port (admittance `Y`), port `1 + i` the `i`-th incident contact (conductance `G_i`). The
/// rest of the junction is one reference `G_rest = W − G_p`.
pub fn port_scattering(
    admittance: &Rat,
    conductances: &[&Rat],
    port: usize,
) -> Result<PortScattering, HnnError> {
    let total = conductances
        .iter()
        .fold(admittance.clone(), |sum, g| sum + *g);
    let own = if port == 0 {
        admittance.clone()
    } else {
        conductances
            .get(port - 1)
            .map(|g| (*g).clone())
            .ok_or(HnnError::Shape {
                what: "a junction port (the storage port, then each contact)",
                expected: conductances.len() + 1,
                found: port,
            })?
    };
    let rest = &total - &own;
    if !own.is_positive() || !rest.is_positive() {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let sum = &own + &rest;
    Ok(PortScattering {
        reflection: (&own - &rest) / &sum,
        transmission: integer(4) * &own * &rest / (&sum * &sum),
    })
}
