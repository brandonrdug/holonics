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
//! bound      |chart + split| ≤ ‖ω‖₁ (δ_t ‖r‖∞ + ‖M_t‖∞ u) + (u/2)(‖C(ŵ′ + w′)‖₁ + ‖K_t(û′ + u′)‖₁)
//! ```
//!
//! [proved-derived; implemented-exact] **The executed solve's bound** ([`ResonatorStep::bound`]).
//! The phase's chart `X̂` carries the certificate every chart of the word carries (the element's
//! and the contact's, `hnn::chart`): `δ_t = ‖1 − M_t X̂‖∞`, zero for the exact inverse. The element
//! reads its chart's image unsplit, so its bound is `‖x̄‖₁ δ ‖operand‖∞`; the resonator carries its
//! solved rate on `2^(−L_w)ℤ` before the state reads it, as the contact carries its `ζ`, so the
//! bound gains the split's term: `M_t ω − r = M_t(ω − X̂ r) − (1 − M_t X̂) r`, and error feedback
//! keeps `|ω − X̂ r|∞ < u = 2^(−L_w)` (the two remainders lie in one half-open cell), hence
//! `|⟨ω, M_t ω − r⟩| ≤ ‖ω‖₁ (δ_t ‖r‖∞ + ‖M_t‖∞ u)` with `‖·‖∞` the largest absolute row sum. The
//! state's split is `E(û′, ŵ′) − E(u′, w′) = ½⟨ŵ′ − w′, C(ŵ′ + w′)⟩ + ½⟨û′ − u′, K_t(û′ + u′)⟩` with
//! each coordinate within `u`, the contact's split bound. Under the exact law both terms and the
//! bound are zero (Lean `HNN/Ring.{loaded_solve_chart_bound, loaded_state_split_bound}`). The
//! chart term no longer absorbs a wrong solve: an executed rate off the certified chart leaves its
//! chart term above the bound, and [`ResonatorStep::closes`],
//! `hnn::word::{FieldBalance, WordBalance}::closes` refuse it.
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
//! [definition; agent-inferred] **The resonator is loaded at the ring storage port.** The junction
//! sends `(b,c)` to the ring element, which returns `e`; the resonator is driven by that carried
//! element output and returns `s′ = e − (2/Y)ω` to the ring's next storage. The return composes the
//! resonator's two-state recurrence before the element and junction transposes. Its port work
//! `P_r = (hY/4)(|e|² − |s′|²)` cancels the field's signed loaded-port term `−P_r`; the remaining
//! split and solve-chart residuals stay explicit. The mode state is word-local and is dropped with
//! the word; the constitution's gains alone may persist through deposition. A ring without a
//! declared resonator retains the earlier element path exactly. All material is read at the
//! producing cut, and the pump selects its predeclared phase within the word:
//!
//! ```text
//! b = 2v − s, c = v − s                 junction Swing
//! e = element(b, c)                    the existing passive/skew/contrast element
//! M_t = 2C + (h/Y)I + hD + (h²/2)K_t
//! M_t ω = 2Cw + h e − hK_t u           the resonator's local solve
//! u′ = u + hω, w′ = 2ω − w
//! s′ = e − (2/Y)ω                      the returned wave reaches the next junction
//!
//! return, with covectors on (s′, u′, w′), the resonator reversed before the element:
//! z̄ = h ū′ + 2w̄′ − (2/Y)s̄′, r̄ = X_tᵀ z̄
//! ē = s̄′ + h r̄, ū = ū′ − hK_tᵀr̄, w̄ = −w̄′ + 2Cᵀr̄
//! material variation = ⟨r̄, 2δC(w−ω) − hδDω − hδK_t(u+hω/2)⟩
//! ```
//!
//! The field's wave-energy change across `e → s′` is the negative of the resonator's port work;
//! their sum closes with pump, dissipation, chart and split terms. The executed element output is
//! carried before it drives the resonator. A carried returned wave has a separate remainder and
//! wave-energy split residual in the field identity; the resonator's own state-energy split keeps
//! its meaning. The source-opening remainder stays with the element's error-feedback stream, and
//! the inserted returned-wave stream starts at zero remainder: the declared composition of the two
//! lattice charts, with every remaining and released term counted, not a uniqueness claim about
//! chart choice. `X_t` is the solve actually executed: the exact inverse law and the declared chart
//! pullback keep their separate scopes, and a rounding is not differentiated as a smooth map.
//! Reached material covectors enter the current deposition consumer and change a later word.
//!
//! [definition; agent-inferred] **The declared material family.** Each loaded ring carries four
//! real scalar amplitudes on its locus lattice: `C = g_C² C₀`, `K = g_K² K₀`, `D = g_D² D₀` and the
//! pump strength `p = g_P² p₀`. The bases, pump axis and pump step are immutable declaration
//! operands. The gain covectors contract the material variation with `2g` times its base, which
//! keeps `C, D` positive semidefinite and the signed stiffness base. A gain never reaches zero by
//! deposition: a step whose carried gain would be `≤ 0` carries it to `⌊(q + 1)/2⌋ 2^(−L)` for
//! `g = q 2^(−L)` (`g/2` for even `q`, toward `g` for odd `q`, holding at `q = 1`; Lean
//! `HNN/Ring.gain_backtrack_midpoint`), and the deposit receipt names each substitution
//! (`DepositReading::backtracks`); releasing a family belongs to campaign 3's collapse law. The gain
//! lattice follows the lattice rule with the ring's realified width as its fan-in
//! (`field::lattice_exponent`). Deposition re-certifies every pump phase before atomic publication
//! and refuses a failing candidate. This is the admitted learning family, not a claim of arbitrary
//! matrix or clock learning; the retained gains, their remainders and statistics are counted in the
//! constitution, and the next word reads them. [historical] The source: campaign 2's resonator
//! received the junction wave but returned none, and no comparison covector reached its material
//! (September 26; its receipt, the fixed source-ring family losing to the default field, is in
//! `research/records/2026-09-26_THE_RESONATOR_RETURNS_ITS_WAVE_AND_THE_COMPARISON_REACHES_ITS_MATERIAL.md`).
//!
//! [definition; agent-inferred] **The pump's phases are finite.** The pump carrier advances by a
//! declared rational rotation per tick; the only rational rotations of finite order in the plane are
//! the quarter turns, so the pump's step is one of them ([`PumpStep`]) and a word visits at most four
//! pump phases, each with its own operator and chart. A pump of infinite order would give each tick
//! its own operator; it is not declared.
//!
//! [definition; agent-inferred] **The pumped passage** ([`PumpedRing`], [`PumpedPassage`]; the
//! ring-search experiment's driver, `research/notebook/hnn_design/hnn_ring_search.rs`). A ring's
//! resonator runs through a declared schedule of [`PumpStage`]s that moves only the pump's strength
//! (storage, stiffness, dissipation and the pump's axis and step are refused unless shared). Each
//! stage's operands are solved once at the cut ([`PumpedRing::new`]), every tick is the resonator's
//! own [`ResonatorOperands::step`] driven through its storage port, and each stage's pump starts at
//! its phase 0. The sheets of the displacement ([`sheets`]) are read after every tick from a declared
//! first read: past the bifurcation (`K_t` negative on the axis) the in-phase coordinate grows on its
//! side and the sheet holds, a lock; unpumped the ring turns and its sheet does not hold. A change of
//! strength injects `½⟨u, (K_new − K_old) u⟩`, which no tick carries, so the passage closes when
//! every tick closes and `E_end − E_start = Σ_ticks (pump + port − dissipation + chart + split) +
//! Σ_switches ½⟨u, (K_new − K_old) u⟩` ([`PumpedPassage::closes`]). Its declared work counts the
//! motion, not the receipt: a tick `6n² + 15n` on the lattices (`6n² + 6n` exact) at realified width
//! `n` ([`tick_work`]: three dense products, nine vector operations and three carried splits a
//! coordinate), a sheet read `2n` ([`read_work`]), and each stage's preparation `n³ + 6n²` plus its
//! solve, `2n³` exact or `2n³(1 + 3·steps)` for the chart's Newton–Schulz refinement
//! ([`PumpedRing::solve_work`]). The executed balance each tick forms is not counted.
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
//! | `loaded_word_stage_balance`, `loaded_tick_executed_interconnection_balance` | [`ResonatorOperands::step`], `hnn::word::{FieldBalance, WordBalance}` |
//! | `loaded_tick_adjoint_pairing`, `loaded_material_rate_tangent`, `loaded_tick_material_variation` | [`ResonatorOperands::solve_transpose`], `hnn::port::Word::pull_back`, `hnn::reference::compose` |
//! | `loaded_gain_family_increment`, `loaded_gains_preserve_storage_dissipation`, `ring_material_commit_work` | [`ResonatorMaterial::with_gains`], `hnn::constitution::Constitution::deposited`, `hnn::word::PowerForm::deposition_work` |
//! | `two_port_reference_balance` | [`port_scattering`], [`PortScattering`] |
//! | `ring_crossings_are_epoch_ticks` | [`RingClock::over`] |
//! | `pump_half_turn_invariant`, `pump_blind_to_sheets`, `locked_sheet_receiver_face` | [`PumpDeclaration`], [`sheets`] |
//! | `loaded_solve_chart_bound`, `loaded_state_split_bound` (with `abs_mulVec_le_rowNorm`, `abs_dot_le_l1`) | [`ResonatorStep::bound`], [`ResonatorStep::closes`] |
//! | `gain_backtrack_midpoint` | `hnn::constitution::GainBacktrack`, [`ResonatorMaterial::with_gains`] |
//! | `ring_tick_executed_energy_balance`, `ring_material_commit_work` (the switch's `½⟨u, ΔK u⟩`), `pump_blind_to_sheets` | [`PumpedRing::pass`], [`PumpedPassage::closes`] |

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

    /// The same pump family at a new nonnegative strength.
    pub fn with_strength(&self, strength: Rat) -> Result<Self, HnnError> {
        Self::new(strength, self.axis.clone(), self.step)
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
/// width; `C, D ⪰ 0`), and its pump. The immutable base forms are declared; four squared scalar
/// amplitudes are learned at the ring's loaded port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonatorMaterial {
    capacity: ExactRatMatrix,
    stiffness: ExactRatMatrix,
    dissipation: ExactRatMatrix,
    pump: Option<PumpDeclaration>,
    base_capacity: ExactRatMatrix,
    base_stiffness: ExactRatMatrix,
    base_dissipation: ExactRatMatrix,
    base_pump: Option<PumpDeclaration>,
    gains: [Rat; 4],
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
            base_capacity: capacity.clone(),
            base_stiffness: stiffness.clone(),
            base_dissipation: dissipation.clone(),
            base_pump: pump.clone(),
            capacity,
            stiffness,
            dissipation,
            pump,
            gains: std::array::from_fn(|_| Rat::one()),
        })
    }

    /// The trainable amplitudes of the declared storage, stiffness, dissipation and pump forms.
    /// Their squares scale immutable declared bases, so positive semidefiniteness is structural.
    pub fn gains(&self) -> &[Rat; 4] {
        &self.gains
    }

    /// Rebuild the material from its declared forms and squared scalar amplitudes. The caller
    /// certifies the candidate at its ring's hop before publication.
    ///
    /// [definition; agent-inferred] **Every amplitude is positive.** `g` and `−g` give one form
    /// (`g²`), so the positive sheet is the chart; a zero amplitude would zero its family's covector
    /// `2g·feature` for every later word, a release that deposition never makes. A family's release
    /// belongs to campaign 3's collapse law, with its receipt; a deposit step that would carry an
    /// amplitude to `g ≤ 0` backtracks instead (`hnn::constitution::GainBacktrack`). A
    /// nonpositive amplitude is refused here.
    pub fn with_gains(&self, gains: [Rat; 4]) -> Result<Self, HnnError> {
        if gains.iter().any(|gain| !gain.is_positive()) {
            return Err(HnnError::Resonator {
                ring: usize::MAX,
                what: "a resonator gain amplitude is positive (release belongs to the collapse)",
            });
        }
        let scale = |form: &ExactRatMatrix, gain: &Rat| form.scaled(&(gain * gain));
        let pump = self
            .base_pump
            .as_ref()
            .map(|pump| pump.with_strength(pump.strength() * &gains[3] * &gains[3]))
            .transpose()?;
        Ok(Self {
            capacity: scale(&self.base_capacity, &gains[0]),
            stiffness: scale(&self.base_stiffness, &gains[1]),
            dissipation: scale(&self.base_dissipation, &gains[2]),
            pump,
            base_capacity: self.base_capacity.clone(),
            base_stiffness: self.base_stiffness.clone(),
            base_dissipation: self.base_dissipation.clone(),
            base_pump: self.base_pump.clone(),
            gains,
        })
    }

    /// Immutable declared bases for the four gain coordinates.
    pub fn gain_bases(
        &self,
    ) -> (
        &ExactRatMatrix,
        &ExactRatMatrix,
        &ExactRatMatrix,
        Option<&Rat>,
    ) {
        (
            &self.base_capacity,
            &self.base_stiffness,
            &self.base_dissipation,
            self.base_pump.as_ref().map(PumpDeclaration::strength),
        )
    }

    /// The immutable declared pump chart, before its learned amplitude is applied.
    pub fn base_pump(&self) -> Option<&PumpDeclaration> {
        self.base_pump.as_ref()
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
/// lattice chart (the lattice word) with its reading.
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

    fn apply_transpose(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        match self {
            Self::Exact(inverse) => Ok(inverse.transpose()?.apply(vector)?),
            Self::Chart(chart) => chart.apply_transpose(vector),
        }
    }
}

/// One pump phase's operands: its stiffness `K_j`, its operator `M_j` with its largest absolute
/// row sum `‖M_j‖∞`, and its executed solve.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Phase {
    stiffness: ExactRatMatrix,
    operator: ExactRatMatrix,
    operator_norm: Rat,
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
    /// The element output that drives this loaded port.
    pub drive: Vec<Rat>,
    /// Resonator state before the tick.
    pub input: [Vec<Rat>; 2],
    /// The exact right side of the phase solve before its executed chart.
    pub right: Vec<Rat>,
    /// The returned storage wave `drive − (2/Y) rate` before the word's carried split.
    pub output: Vec<Rat>,
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
    /// **The certified bound on `|chart + split|`** (module header): `‖ω‖₁(δ‖r‖∞ + ‖M‖∞u)` for the
    /// executed solve and `(u/2)(‖C(ŵ′ + w′)‖₁ + ‖K(û′ + u′)‖₁)` for the state's split; zero under
    /// the exact law.
    pub bound: Rat,
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
    /// `after − before = pump + port − dissipation + chart + split`, and the executed solve's and
    /// split's residual lies within its certified bound, `|chart + split| ≤ bound`.
    pub fn closes(&self) -> bool {
        &self.after - &self.before
            == &self.pump + &self.port - &self.dissipation + &self.chart + &self.split
            && (&self.chart + &self.split).abs() <= self.bound
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
                let operator_norm = (0..n)
                    .map(|i| {
                        operator
                            .row(i)
                            .expect("in range")
                            .iter()
                            .map(|x| x.abs())
                            .sum::<Rat>()
                    })
                    .max()
                    .unwrap_or_else(Rat::zero);
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
                    operator_norm,
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

    /// The pump phases the word visits.
    pub fn phases(&self) -> usize {
        self.phases.len()
    }

    /// `h`, the hop.
    pub fn hop(&self) -> &Rat {
        &self.step
    }

    /// The executed chart of pump phase `j`, when the word is on its lattices (a realization off
    /// the host executes the same chart).
    pub fn chart_words(&self, phase: usize) -> Option<&ChartWords> {
        match &self.phases[phase].solve {
            PhaseSolve::Chart(chart) => Some(chart),
            PhaseSolve::Exact(_) => None,
        }
    }

    /// The operator `M_j` of pump phase `j`.
    pub fn operator(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].operator
    }

    /// The pumped stiffness `K_j`.
    pub fn stiffness(&self, phase: usize) -> &ExactRatMatrix {
        &self.phases[phase].stiffness
    }

    /// `‖M_j‖∞`, the operator's largest absolute row sum.
    pub fn operator_norm(&self, phase: usize) -> &Rat {
        &self.phases[phase].operator_norm
    }

    /// `δ_j = ‖1 − M_j X̂_j‖∞`, the executed chart's certificate; zero for the exact inverse.
    pub fn certificate(&self, phase: usize) -> Rat {
        self.phases[phase]
            .reading
            .as_ref()
            .map_or_else(Rat::zero, |reading| reading.certificate.clone())
    }

    /// Replace pump phase `j`'s executed solve by `solve`, its certificate kept: the wrong solve of
    /// the bound's own test.
    #[cfg(test)]
    pub(crate) fn with_executed_solve(mut self, phase: usize, solve: ExactRatMatrix) -> Self {
        self.phases[phase].solve = PhaseSolve::Exact(solve);
        self
    }

    /// Apply the transpose of the executed phase solve to a covector.
    pub fn solve_transpose(&self, phase: usize, covector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.phases[phase].solve.apply_transpose(covector)
    }

    /// Apply the executed phase solve to a right-side variation.
    pub fn solve(&self, phase: usize, right: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        self.phases[phase].solve.apply(right)
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
        // |⟨ω, M ω − r⟩| ≤ ‖ω‖₁(δ‖r‖∞ + ‖M‖∞u) and |E(x̂) − E(x)| ≤ (u/2)(‖C(ŵ + w)‖₁ + ‖K(û + u)‖₁).
        let bound = match lattice {
            Some(lattice) => {
                let unit = lattice.unit();
                let solve = l1(&rate)
                    * (self.certificate(phase) * sup(&right)
                        + &self.phases[phase].operator_norm * &unit);
                let stored = capacity.apply(&add(&velocity, &velocity_image))?;
                let stiffened = stiffness.apply(&add(&displacement, &displacement_image))?;
                solve + unit * (l1(&stored) + l1(&stiffened)) / integer(2)
            }
            None => l1(&rate) * self.certificate(phase) * sup(&right),
        };
        Ok(ResonatorStep {
            drive: drive.to_vec(),
            input: [u.to_vec(), w.to_vec()],
            right,
            output: out,
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
            bound,
            remainders: ResonatorRemainders {
                rate: rate_remainder,
                state: [displacement_remainder, velocity_remainder],
            },
        })
    }
}

// -------------------------------------------------------------------------------------------
// the pumped passage

/// [definition; agent-inferred] **One stage of a pump schedule**: the ring's resonator at the
/// stage's pump strength, and the ticks it runs. The stages of one passage declare the same storage,
/// stiffness and dissipation and the same pump axis and step; only the strength moves (module
/// header, "The pumped passage").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpStage {
    pub material: ResonatorMaterial,
    pub ticks: usize,
}

/// [definition; agent-inferred] **A pumped passage's declared work** (module header): elementary
/// exact operations, each rational or integer addition, subtraction, multiplication, division,
/// comparison or carry counted as one, of the solves' construction (`solves`, charged once per
/// [`PumpedRing`]) and of each passage's dynamics and sheet reads. The executed balance every tick
/// also forms is the law's receipt, not the motion, and is not counted.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PassageWork {
    pub dynamics: u64,
    pub reads: u64,
}

impl PassageWork {
    pub fn total(&self) -> u64 {
        self.dynamics + self.reads
    }
}

/// [definition] **A pumped passage's receipt**: the carried state at its end; the sheets read after
/// each tick from the declared first read on, in tick order (the lock readout); the ticks run and
/// those whose executed balance closed ([`ResonatorStep::closes`]); the pump's work at each change of
/// strength, `½⟨u, (K_new − K_old) u⟩`, which no tick carries; the storage at the start and the end;
/// the sum of every tick's balance terms; and the declared work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpedPassage {
    pub state: [Vec<Rat>; 2],
    pub sheets: Vec<Vec<bool>>,
    pub ticks: usize,
    pub closed: usize,
    pub switch_work: Vec<Rat>,
    pub start_energy: Rat,
    pub end_energy: Rat,
    pub terms: Rat,
    pub work: PassageWork,
}

impl PumpedPassage {
    /// **The passage closes**: every tick's executed balance closes, and the storage telescopes
    /// across the stages, `E_end − E_start = Σ_ticks (pump + port − dissipation + chart + split) +
    /// Σ_switches ½⟨u, (K_new − K_old) u⟩`.
    pub fn closes(&self) -> bool {
        self.closed == self.ticks
            && &self.end_energy - &self.start_energy
                == &self.terms + self.switch_work.iter().sum::<Rat>()
    }
}

/// [definition; agent-inferred] **A ring's resonator prepared for pumped passages** (module header):
/// each stage's operands at the cut, solved once (the exact inverse, or the word lattice's chart),
/// the pump's axis whose sheets are read, and the declared work of that preparation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PumpedRing {
    ring: usize,
    stages: Vec<(ResonatorOperands, usize)>,
    axis: Carrier,
    transient: Option<Lattice>,
    solve_work: u64,
}

/// The declared work of one tick's dynamics at width `n` (module header): three dense
/// matrix–vector products `6n² − 3n`, the vector operations `9n`, and on the lattice the three
/// carried splits `9n`.
pub fn tick_work(width: usize, lattice: bool) -> u64 {
    let n = width as u64;
    6 * n * n - 3 * n + if lattice { 18 * n } else { 9 * n }
}

/// The declared work of reading one tick's sheets at width `n`: two products, a sum and a
/// comparison a node.
pub fn read_work(width: usize) -> u64 {
    2 * width as u64
}

impl PumpedRing {
    /// **Prepare a ring's pumped passages** (module header): every stage certified and solved at the
    /// cut. Refused without a stage, without a declared pump (its axis reads the sheets, at zero
    /// strength or above), or when two stages differ in anything but the pump's strength.
    pub fn new(
        ring: usize,
        admittance: &Rat,
        hop: &Rat,
        lattice: Option<&WordLattice>,
        stages: &[PumpStage],
    ) -> Result<Self, HnnError> {
        let first = stages.first().ok_or(HnnError::Resonator {
            ring,
            what: "a pumped passage has at least one stage",
        })?;
        let undeclared = || HnnError::Resonator {
            ring,
            what: "a pumped passage declares its pump (its axis reads the sheets), at zero strength or above",
        };
        let declared = first.material.pump().ok_or_else(undeclared)?;
        for stage in stages {
            let pump = stage.material.pump().ok_or_else(undeclared)?;
            if stage.material.forms() != first.material.forms()
                || pump.axis() != declared.axis()
                || pump.step() != declared.step()
            {
                return Err(HnnError::Resonator {
                    ring,
                    what: "a pumped passage's stages share the storage, stiffness, dissipation and the pump's axis and step; only the strength moves",
                });
            }
        }
        let n = first.material.width() as u64;
        let mut solve_work = 0u64;
        let mut prepared = Vec::with_capacity(stages.len());
        for stage in stages {
            let operands =
                ResonatorOperands::at_cut(ring, &stage.material, admittance, hop, lattice)?;
            // Per pump phase: the certificate's elimination n³, forming the operator 6n², and the
            // solve: the exact inverse 2n³, or the chart's (1 + 3·steps) products of 2n³.
            for phase in 0..operands.phases() {
                let solve = match operands.charts().get(phase) {
                    Some(reading) => 2 * n * n * n * (1 + 3 * u64::from(reading.steps)),
                    None => 2 * n * n * n,
                };
                solve_work += n * n * n + 6 * n * n + solve;
            }
            prepared.push((operands, stage.ticks));
        }
        Ok(Self {
            ring,
            stages: prepared,
            axis: declared.axis().clone(),
            transient: lattice.map(WordLattice::transient),
            solve_work,
        })
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// The realified width.
    pub fn width(&self) -> usize {
        self.stages[0].0.width()
    }

    /// The ticks of one passage: every stage's.
    pub fn ticks(&self) -> usize {
        self.stages.iter().map(|(_, ticks)| ticks).sum()
    }

    /// The declared work of the preparation (module header).
    pub fn solve_work(&self) -> u64 {
        self.solve_work
    }

    /// **One pumped passage** (module header) from `initial = [u, w]`: at every tick `t` the drive
    /// `drive(t)` enters the ring's storage port and the stage's operands tick it (each stage's pump
    /// from its phase 0), the sheets of `u` are read after every tick from `first_read` on, and each
    /// change of stage books the pump's work on the carried state.
    pub fn pass(
        &self,
        initial: [Vec<Rat>; 2],
        first_read: usize,
        mut drive: impl FnMut(usize) -> Vec<Rat>,
    ) -> Result<PumpedPassage, HnnError> {
        let n = self.width();
        if initial[0].len() != n || initial[1].len() != n {
            return Err(HnnError::Shape {
                what: "a pumped passage's initial state (the ring's realified width)",
                expected: n,
                found: initial[0].len().min(initial[1].len()),
            });
        }
        let lattice = self.transient.is_some();
        let mut state = initial;
        let mut remainders = ResonatorRemainders::zero(n);
        let start_energy = self.stages[0].0.energy_at(0, &state[0], &state[1])?;
        let mut work = PassageWork::default();
        let (mut terms, mut switch_work) = (Rat::zero(), Vec::new());
        let (mut sheets_read, mut closed, mut tick) = (Vec::new(), 0usize, 0usize);
        let mut last: Option<(&ResonatorOperands, usize)> = None;
        for (operands, ticks) in &self.stages {
            if let Some((previous, phase)) = last {
                let before = previous.energy_at(phase, &state[0], &state[1])?;
                switch_work.push(operands.energy_at(0, &state[0], &state[1])? - before);
            }
            for local in 0..*ticks {
                let beta = drive(tick);
                let step = operands.step(
                    local,
                    &beta,
                    [&state[0], &state[1]],
                    &remainders,
                    self.transient.as_ref(),
                )?;
                work.dynamics += tick_work(n, lattice);
                closed += usize::from(step.closes());
                terms += &step.pump + &step.port - &step.dissipation + &step.chart + &step.split;
                remainders = step.remainders().clone();
                state = step.state;
                if tick >= first_read {
                    sheets_read.push(sheets(&state[0], &self.axis));
                    work.reads += read_work(n);
                }
                tick += 1;
            }
            let phase = if *ticks == 0 {
                0
            } else {
                operands.phase_at(ticks - 1)
            };
            last = Some((operands, phase));
        }
        let (operands, phase) = last.expect("a prepared ring has a stage");
        let end_energy = operands.energy_at(phase, &state[0], &state[1])?;
        Ok(PumpedPassage {
            state,
            sheets: sheets_read,
            ticks: tick,
            closed,
            switch_work,
            start_energy,
            end_energy,
            terms,
            work,
        })
    }
}

/// `‖x‖₁`.
fn l1(vector: &[Rat]) -> Rat {
    vector.iter().map(|x| x.abs()).sum()
}

/// `‖x‖∞`.
fn sup(vector: &[Rat]) -> Rat {
    vector
        .iter()
        .map(|x| x.abs())
        .max()
        .unwrap_or_else(Rat::zero)
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
