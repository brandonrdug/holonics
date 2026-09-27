//! **A loaded ring's modes and their future quotient** (campaign 3, first construction; Lean
//! `HNN/ModeQuotient`).
//!
//! [definition] A loaded ring at a fixed publication (the loaded resonator, [`crate::hnn::ring`]): its
//! material read at the producing cut, its pump at phase `t mod P` of the word's tick `t`. Under the
//! exact law its word-local state `x = (u, w) ∈ ℚ^(2n)` ticks as one linear system per pump phase,
//! driven by the element output `e` and returning the wave `s′` to the ring's next junction:
//!
//! ```text
//! M_t ω = 2Cw + he − hK_t u,   u′ = u + hω,   w′ = 2ω − w,   s′ = e − (2/Y)ω
//! x′ = T_t x + B_t e           s′ = ρ_t x + D_t e
//! ```
//!
//! [`LoadedRing::at_cut`] forms `(T_t, B_t, ρ_t, D_t)` column by column from the owner's exact tick
//! ([`ResonatorOperands::step`] on the unit states and drives), so the law has no second copy here.
//! A lattice chart's executed solve is not the law, and its operands are refused.
//!
//! [definition] **The admitted receivers.** Receiver `0` is the loaded port: it reads `ρ_t` at every
//! phase, the wave the ring returns to the field. A declared [`StateReceiver`] reads the state at the
//! pump phases it names (a cycle receiver, for example, once per cycle). The present family is every
//! receiver that reads at phase `0`, the tick at the cut; the admitted future family is every
//! receiver at every later tick of the pump's cycle. It contains the present one, so
//! `ker F_future ⊆ ker F_now` (Lean `Holarchy/Hearing.HearingLaw.futureNull_le_ker_present`):
//! present silence alone releases nothing.
//!
//! [proved-derived; implemented-exact] **The admitted words are the pump's cycle, read through its
//! period** (Lean `periodic_lift_exact`, `cycle_mul_add`). With `Φ(0) = 1` and `Φ(t+1) = T_t Φ(t)`,
//! periodicity gives `Φ(mP + k) = Φ(k) T_P^m` for `T_P = Φ(P) = T_(P−1)⋯T_0`, so receiver `r`'s
//! reading at tick `t = mP + k` is `ρ_(r,k) Φ(k)` after `m` letters of the one period navigator
//! `T_P`. The requests `(r, t)` and `((r, k), m)` correspond one to one with equal readings, so the
//! kernel of [`FaceMap`] on the navigator `{T_P}` and the phase-offset receivers `ρ_(r,k) Φ(k)`,
//! `k < P`, is exactly the admitted future kernel `K_adm` ([`ModeQuotient::admitted`]). The phase
//! family read over arbitrary words would admit words the pump never runs.
//!
//! [proved-derived; implemented-exact] **One chart for every phase** (Lean `phase_kernel_le_lift`,
//! `shared_chart_le_phase_kernel`).
//! A retention chart `V` that serves every phase closes `V T_t = T̄_t V` and `ρ_(r,t) = ρ̄_(r,t) V`
//! exactly when `ker V` is carried by every `T_t` and read by no `ρ_(r,t)`. The largest such kernel
//! is the kernel `K_rel` of [`FaceMap`] on the phase family (navigators `T_t`, receivers `ρ_(r,t)`,
//! [`ModeQuotient::release`]), whose [`FaceMap::quotient`] checks both squares exactly and whose
//! sources descend as `B̄_t = V B_t`. Every admitted reading is a reading of that family after the
//! cycle's word, so `K_rel ⊆ K_adm ⊆ ker F_now`. A direction of `K_adm` outside `K_rel` is silent to
//! the whole admitted future, but a chart shared by every phase fails a square on it: it is retained
//! with the phase-family reading that separates it. The pumped witness: with `K = 0`, `C = 1` and a
//! half-turn pump, the pair `(u, (h/2)K_0 u)` moves no rate at phase `0` and ticks to
//! `(u, −(h/2)K_0 u)`, which moves none at phase `1`: the cycle never lets the port hear it. The
//! phase-`1` port would hear the pair itself (`2hK_0 u`), and a chart shared by both phases must
//! factor that reading, so one chart cannot drop it. It stores `½⟨u, K_0 u⟩ + (h²/8)|K_0 u|²`; a
//! phase-indexed chart family `V_(t+1) T_t = T̄_t V_t` could drop it, and one chart's release never
//! drops stored energy (below).
//!
//! [proved-derived; implemented-exact] **Every present-silent coordinate is accounted for**
//! ([`ModeQuotient::silent`]). The present blind subspace `N = ker F_now` has a basis adapted to
//! `K_rel ⊆ K_adm ⊆ N`: each direction of `K_rel` is [`Silence::Released`]; each further direction
//! of `K_adm` is [`Silence::SquareFails`] with the shortest phase-family word and reading that
//! separate it (the blind-subspace recursion descended one letter per level); each further direction
//! of `N` is [`Silence::Heard`] with the first tick and receiver of the admitted cycle that read it.
//!
//! [proved-derived; implemented-exact] **The released part stores nothing** (Lean
//! `released_pair_storage_null`). The port is admitted at every phase, so a released `(u, w)` has a
//! zero rate at every phase, its tick is `(u, −w)`, which is released too, and `2Cw = hK_t u`,
//! `−2Cw = hK_t u` give `Cw = 0` and `K_t u = 0`. The storage form `Q_t = diag(K_t, C)` annihilates
//! `K_rel` at every phase: the split `x = x_ret + x_rel` is `Q_t`-orthogonal (so `C`-orthogonal) for
//! every complement, `E_t(x + k) = E_t(x)` for `k ∈ K_rel`, and the storage descends to the retained
//! ring. This holds for every loaded ring whose port is admitted, not only for the fixtures.
//!
//! [proved-derived; implemented-exact] **The descended ring runs** (Lean `descended_run`,
//! `descended_run_reads`; [`ModeQuotient::run`]): `q′ = T̄_t q + B̄_t e`, `s′ = ρ̄_(0,t) q + D_t e`
//! from `q = V x` returns the full ring's wave at every tick for every drive sequence, the equation
//! at the consumer `decode(T_native(encode x)) = T(x)` with `V` the encoder and the port the decoder.
//!
//! [proved-derived; implemented-exact] **The learning covector factors through the chart** (Lean
//! `descended_costate`, `descended_drive_covector`, `descended_gain`, `gain_fibre_invariant`;
//! [`ModeQuotient::pull_back`]). A declared comparison puts covectors on admitted readings: `s̄_t`
//! on the port's returned wave, `ȳ_(r,t)` on the declared receivers. Its costate
//! `λ_t = λ_(t+1) T_t + s̄_t ρ_t + Σ_r ȳ_(r,t) R_r` descends because every tick and reading does:
//! `λ_t = λ̄_t V`, so it vanishes on the release. The drive covector
//! `ē_t = λ̄_(t+1) B̄_t + s̄_t D_t` and the solved covector `r̄_t = X_tᵀ z̄_t = (ē_t − s̄_t)/h` are the
//! full ring's. Gain family `f`'s covector `G_f = Σ_t ⟨r̄_t, φ_(f,t)⟩` pairs its variation
//! `φ = 2δC(w − ω) − hδD ω − hδK_t(u + hω/2)` (`δ = 2g·base`, the loaded resonator; [`Variation`]), a linear
//! reading `F x + H e` with the rate read from the port. It descends exactly when `F` vanishes on
//! the release, and then `F = (F σ) V` for a section `σ` of the chart.
//!
//! [proved-derived; implemented-exact] **The exact condition** (Lean `released_variation_shift`,
//! `solved_pairing_null_iff`, `squared_gain_variation_null`, `half_turn_separates`,
//! `standing_pump_threshold_reads_release`). A released `k` has `C k_w = 0`, `K_t k_u = 0` and zero
//! rate at every phase, so at `x + k` the variation moves by `2δC k_w − hδK_t k_u` alone, and the
//! solved covector ranges over every covector as the port's `s̄` does. Family `f`'s covector is
//! constant on the fibre for every admitted comparison iff `2δ_f C k_w = hδ_f K_t k_u` for every
//! released `k` and every phase. Per family:
//! - **capacity**: always, since `C k_w = g_C² C₀ k_w = 0` with `g_C > 0`;
//! - **dissipation**: always, since `δD` meets only the rate, which is zero on the release;
//! - **stiffness and pump**: iff `K₀ k_u = 0` (equivalently `Π_t k_u = 0`). A pump of order `2`
//!   or `4` holds `ψ` and `ψ + π` in its cycle, `K_t = g_K²K₀ ± g_P²p₀Π`, so a released
//!   displacement lies in `ker K₀ ∩ ker Π`; unpumped, `K = g_K²K₀`. Both factor. They fail exactly
//!   for a standing pump (`P = 1`) at threshold, `(g_K²K₀ + g_P²p₀Π_0) k_u = 0` with
//!   `K₀ k_u ≠ 0`: the pump cancels the stiffness and the mode stands still. The joint scaling
//!   `g_K ∂_(g_K) + g_P ∂_(g_P)` still factors (it pairs `2K_0 k_u = 0`), the separate covectors do
//!   not, and a deposit along either would make the mode heard.
//!
//! [proved-derived; implemented-exact] **In a learning aeon the deposit is a receiver** (Lean
//! `learning_chart_le_kernel`; [`ModeQuotient::learning`]). The four variations at every phase are
//! admitted beside the port and the declared receivers (receiver `1 + m + f`); the chart is the
//! phase family's kernel with them, `K_learn ⊆ K_rel`, the largest one-chart release through which
//! every gain covector descends. A direction of `K_rel` outside `K_learn` is retained as
//! [`Silence::Deposited`] with the deposit's reading that separates it. [`ModeQuotient::of`] reports
//! each family's [`GainDescent`], and its return names no covector for a family that reads its
//! release. On the fixtures every family descends and `K_learn = K_rel`; the standing pump at
//! threshold releases `1` direction frozen and none in a learning aeon.
//!
//! [proved-derived; implemented-exact] **The descended block ticks** (Lean `modeForm_radical`,
//! `descended_form`, `descended_balance_terms`, `descended_balance`; [`ModeQuotient::tick`]).
//! `T̄_t` has no Cayley or two-port form. The descended block is its own exact linear tick
//! `q′ = T̄_t q + B̄_t e`, `s′ = ρ̄_(0,t) q + D_t e`, with the rate read from the port,
//! `ω = (Y/2)(e − s′)`, and the storage form `Q̄_t = σᵀ Q_t σ`. The release lies in the radical of
//! `Q_t = diag(K_t, C)`, so `Q_t = Vᵀ Q̄_t V` and `E_t(x) = ½⟨Vx, Q̄_t Vx⟩` for every lift. Its balance
//!
//! ```text
//! ½⟨q′, Q̄_t q′⟩ − ½⟨q, Q̄_(t−1) q⟩ = ½⟨q, (Q̄_t − Q̄_(t−1)) q⟩ + (hY/4)(|e|² − |s′|²) − h⟨ω, D ω⟩
//! ```
//!
//! is the full ring's at every lift of `q`, term for term: storage before and after, pump work,
//! port work and dissipation. The chart and split terms are zero under the exact law.
//!
//! | Lean `HNN/ModeQuotient` | Rust |
//! |---|---|
//! | `cycle_mul_add`, `periodic_lift_exact` | [`LoadedRing::cycle`], [`LoadedRing::period`], [`ModeQuotient::admitted`] |
//! | `phase_kernel_le_cycle`, `phase_kernel_le_lift`, `wordMap_cycleWord`, `shared_chart_le_phase_kernel` | [`ModeQuotient::release`], [`ModeQuotient::of`] (the nesting checked) |
//! | `descended_run`, `descended_run_reads` | [`ModeQuotient::run`] |
//! | `released_pair_storage_null` | [`ModeQuotient::released`] (checked at the consumer, `tests/modes.rs`) |
//! | `descended_costate`, `costate_null_on_release`, `descended_drive_covector`, `descended_gain`, `gain_fibre_invariant` | [`ModeQuotient::pull_back`], [`DescendedReturn`] |
//! | `released_variation_shift`, `solved_pairing_null_iff`, `squared_gain_variation_null`, `half_turn_separates`, `standing_pump_threshold_reads_release` | [`Variation`], [`ModeQuotient::gain_descent`], [`GainDescent`] |
//! | `learning_chart_le_kernel` | [`ModeQuotient::learning`], [`Silence::Deposited`] |
//! | `modeForm_radical`, `descended_form`, `descended_balance_terms`, `descended_balance` | [`ModeQuotient::storage`], [`ModeQuotient::tick`], [`DescendedTick`] |
//! | `Compression/Core/FaceMap.{ker_faceMap_invariant, kernelClass_after_word, kernelReceiverQuotient}` | [`FaceMap::quotient`], [`Retention::section`] |
//!
//! [definition; agent-inferred] **Why its own owner.** [`crate::hnn::retention`] releases whole
//! loci at an aeon boundary, structurally, on the field's sparsity; this owner releases directions
//! inside one loaded ring's state by their values (the value kernel that
//! [`crate::hnn::AeonBoundary`] names as campaign 3's). Its objects are the ring's modes and their
//! receivers, not loci, so they sit beside [`crate::hnn::ring`]'s exact tick and the
//! [`FaceMap`] owner they join.
//!
//! [definition] **Scope.** Under the exact law, the material covectors descend through the chart,
//! and a learning aeon admits [`ModeQuotient::learning`]. Not built here: the lattice chart's solve
//! and remainders on the descended block, the card, dormancy across an aeon boundary, founding and
//! far fields.

use num_traits::{One, Zero};

use crate::compression::{CompressionError, FaceMap, Retention};
use crate::hnn::HnnError;
use crate::hnn::ring::{ResonatorOperands, ResonatorRemainders};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, is_zero, matrix, scale, sub, zeros};
use crate::ratio::{Rat, integer};
use crate::receiver::standing::{NavigatorFamily, ReceiverReading};

/// The gain families in the material's order: capacity, stiffness, dissipation, pump
/// ([`crate::hnn::ring::ResonatorMaterial::gains`]).
pub const GAIN_FAMILIES: usize = 4;

// -------------------------------------------------------------------------------------------
// the loaded ring's exact operators

/// [definition] **A gain family's material variation at one pump phase** (the loaded resonator): the vector
/// `2δC(w − ω) − hδD ω − hδK_t(u + hω/2)` along the family's direction `δ = 2g·base`, a linear
/// reading `φ = F x + H e` of the state and the drive (the rate read from the port,
/// `ω = (Y/2)(e − s′)`). The family's gain covector is `Σ_t ⟨r̄_t, φ_t⟩`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Variation {
    /// `F`, the state part (`n × 2n` on the ring, `n × rank V` descended).
    pub state: ExactRatMatrix,
    /// `H`, the drive part, `n × n`.
    pub drive: ExactRatMatrix,
}

impl Variation {
    /// `φ = F x + H e`.
    pub fn apply(&self, state: &[Rat], drive: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        Ok(add(&self.state.apply(state)?, &self.drive.apply(drive)?))
    }
}

/// [definition] **One pump phase of a loaded ring under the exact law**: `x′ = T x + B e` and
/// `s′ = ρ x + D e` on the state `x = (u, w)` and the drive `e`, its storage form and the gain
/// families' variations.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedPhase {
    /// `T_t`, `2n × 2n`.
    pub transport: ExactRatMatrix,
    /// `B_t`, `2n × n`.
    pub source: ExactRatMatrix,
    /// `ρ_t`, `n × 2n`: the returned wave's state part.
    pub reading: ExactRatMatrix,
    /// `D_t`, `n × n`: the returned wave's drive part.
    pub feedthrough: ExactRatMatrix,
    /// `Q_t = diag(K_t, C)`, `2n × 2n`: the storage `E_t(x) = ½⟨x, Q_t x⟩`.
    pub storage: ExactRatMatrix,
    /// The four gain families' variations, in [`GAIN_FAMILIES`] order.
    pub variations: [Variation; GAIN_FAMILIES],
}

/// [definition] **A loaded ring at a fixed publication**: its exact per-phase operators, formed from
/// the owner's tick, with its port's hop, admittance and dissipation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedRing {
    ring: usize,
    width: usize,
    hop: Rat,
    admittance: Rat,
    dissipation: ExactRatMatrix,
    phases: Vec<LoadedPhase>,
}

fn unit(extent: usize, index: usize) -> Vec<Rat> {
    let mut vector = zeros(extent);
    vector[index] = Rat::one();
    vector
}

fn from_columns(rows: usize, columns: &[Vec<Rat>]) -> Result<ExactRatMatrix, HnnError> {
    Ok(matrix(rows, columns.len(), |row, column| {
        columns[column][row].clone()
    })?)
}

/// `[A 0; 0 B]`.
fn block_diagonal(
    upper: &ExactRatMatrix,
    lower: &ExactRatMatrix,
) -> Result<ExactRatMatrix, HnnError> {
    let n = upper.rows();
    Ok(matrix(2 * n, 2 * n, |row, column| {
        match (row < n, column < n) {
            (true, true) => upper.get(row, column).expect("in range").clone(),
            (false, false) => lower.get(row - n, column - n).expect("in range").clone(),
            _ => Rat::zero(),
        }
    })?)
}

/// The selection of the state's half `(u, w) ↦ u` (`half = 0`) or `↦ w` (`half = 1`).
fn half(n: usize, half: usize) -> Result<ExactRatMatrix, HnnError> {
    Ok(matrix(n, 2 * n, |row, column| {
        if column == half * n + row {
            Rat::one()
        } else {
            Rat::zero()
        }
    })?)
}

/// **The four families' variations at one phase** (module header): each family's direction
/// `δ = 2g·base` is `(2/g)` times its present contribution (`C = g_C²C₀`, `K = g_K²K₀`,
/// `D = g_D²D₀`, the pump's `K_t − K = g_P²p₀Π_t`), and the rate is read from the port.
fn variations(
    operands: &ResonatorOperands,
    phase: usize,
    rate: (&ExactRatMatrix, &ExactRatMatrix),
) -> Result<[Variation; GAIN_FAMILIES], HnnError> {
    let material = operands.material();
    let n = material.width();
    let h = operands.hop();
    let (capacity, unpumped, dissipation) = material.forms();
    let gains = material.gains();
    let pump = operands.stiffness(phase).subtract(unpumped)?;
    let direction = |form: &ExactRatMatrix, gain: &Rat| form.scaled(&(integer(2) / gain));
    let zero = ExactRatMatrix::zero(n, n)?;
    let (displacement, velocity) = (half(n, 0)?, half(n, 1)?);
    let (rate_state, rate_drive) = rate;
    let directions = [
        (direction(capacity, &gains[0]), zero.clone(), zero.clone()),
        (zero.clone(), zero.clone(), direction(unpumped, &gains[1])),
        (
            zero.clone(),
            direction(dissipation, &gains[2]),
            zero.clone(),
        ),
        (zero.clone(), zero.clone(), direction(&pump, &gains[3])),
    ];
    let midpoint = displacement.add(&rate_state.scaled(&(h / integer(2))))?;
    let mut families = Vec::with_capacity(GAIN_FAMILIES);
    for (capacity, dissipation, stiffness) in directions {
        // F = 2δC(Π_w − W) − hδD W − hδK(Π_u + (h/2)W),  H = −(2δC + hδD + (h²/2)δK) Z.
        let state = capacity
            .scaled(&integer(2))
            .multiply(&velocity.subtract(rate_state)?)?
            .subtract(&dissipation.scaled(h).multiply(rate_state)?)?
            .subtract(&stiffness.scaled(h).multiply(&midpoint)?)?;
        let drive = capacity
            .scaled(&integer(2))
            .add(&dissipation.scaled(h))?
            .add(&stiffness.scaled(&(h * h / integer(2))))?
            .multiply(rate_drive)?
            .scaled(&integer(-1));
        families.push(Variation { state, drive });
    }
    Ok(families.try_into().expect("four families"))
}

impl LoadedRing {
    /// **The ring's exact operators at the cut** (module header): each phase's columns are the
    /// owner's exact tick at that phase on a unit state (zero drive) and on a unit drive (zero
    /// state); its storage form and the families' variations are read from the owner's forms and
    /// the port. Refused when a phase's executed solve is a lattice chart, which is not the law.
    pub fn at_cut(operands: &ResonatorOperands) -> Result<Self, HnnError> {
        let ring = operands.ring();
        let n = operands.width();
        let extent = 2 * n;
        let rest = ResonatorRemainders::default();
        let (capacity, _, dissipation) = operands.material().forms();
        let half_admittance = operands.admittance() / integer(2);
        let mut phases = Vec::with_capacity(operands.phases());
        for phase in 0..operands.phases() {
            if operands.chart_words(phase).is_some() {
                return Err(HnnError::ModeQuotient {
                    ring,
                    what: "the mode quotient reads the exact law, not a lattice chart's solve",
                });
            }
            // Word tick `phase` lies at pump phase `phase` (`ResonatorOperands::phase_at`).
            let tick = |drive: &[Rat], state: &[Rat]| {
                operands.step(phase, drive, [&state[..n], &state[n..]], &rest, None)
            };
            let (mut transport, mut reading) = (Vec::new(), Vec::new());
            for column in 0..extent {
                let stepped = tick(&zeros(n), &unit(extent, column))?;
                transport.push([stepped.state[0].clone(), stepped.state[1].clone()].concat());
                reading.push(stepped.output);
            }
            let (mut source, mut feedthrough) = (Vec::new(), Vec::new());
            for column in 0..n {
                let stepped = tick(&unit(n, column), &zeros(extent))?;
                source.push([stepped.state[0].clone(), stepped.state[1].clone()].concat());
                feedthrough.push(stepped.output);
            }
            let reading = from_columns(n, &reading)?;
            let feedthrough = from_columns(n, &feedthrough)?;
            // The port returns `s′ = e − (2/Y)ω`, so `ω = W x + Z e` with `W = −(Y/2)ρ_t` and
            // `Z = (Y/2)(1 − D_t)`.
            let rate_state = reading.scaled(&-half_admittance.clone());
            let rate_drive = ExactRatMatrix::identity(n)?
                .subtract(&feedthrough)?
                .scaled(&half_admittance);
            phases.push(LoadedPhase {
                transport: from_columns(extent, &transport)?,
                source: from_columns(extent, &source)?,
                storage: block_diagonal(operands.stiffness(phase), capacity)?,
                variations: variations(operands, phase, (&rate_state, &rate_drive))?,
                reading,
                feedthrough,
            });
        }
        Ok(Self {
            ring,
            width: n,
            hop: operands.hop().clone(),
            admittance: operands.admittance().clone(),
            dissipation: dissipation.clone(),
            phases,
        })
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `n`, the ring's realified width (the drive's and the wave's extent).
    pub fn width(&self) -> usize {
        self.width
    }

    /// `2n`, the state's extent.
    pub fn extent(&self) -> usize {
        2 * self.width
    }

    /// The pump phases, in order.
    pub fn phases(&self) -> &[LoadedPhase] {
        &self.phases
    }

    /// **The cycle's transport** `Φ(t) = T_(t−1 mod P) ⋯ T_0` over the word's first `t` ticks.
    pub fn cycle(&self, ticks: usize) -> Result<ExactRatMatrix, HnnError> {
        let mut transport = ExactRatMatrix::identity(self.extent())?;
        for tick in 0..ticks {
            transport = self.phases[tick % self.phases.len()]
                .transport
                .multiply(&transport)?;
        }
        Ok(transport)
    }

    /// **The period navigator** `T_P = Φ(P)`.
    pub fn period(&self) -> Result<ExactRatMatrix, HnnError> {
        self.cycle(self.phases.len())
    }
}

// -------------------------------------------------------------------------------------------
// the admitted receivers

/// [definition] **A declared receiver of the ring's state** beside its port: its exact reading of
/// `x = (u, w)` and the pump phases at which it reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateReceiver {
    reading: ExactRatMatrix,
    phases: Vec<usize>,
}

impl StateReceiver {
    pub fn new(reading: ExactRatMatrix, phases: Vec<usize>) -> Self {
        Self { reading, phases }
    }

    pub fn reading(&self) -> &ExactRatMatrix {
        &self.reading
    }

    pub fn phases(&self) -> &[usize] {
        &self.phases
    }
}

/// [definition] **What separates a direction**: receiver `receiver` reading at pump phase `phase`
/// after the word `word` of phase navigators, its last letter acting first. Receiver `0` is the
/// port, `j + 1` the `j`-th declared, and in a learning aeon `1 + m + f` (`m` declared) is gain
/// family `f`'s variation, the deposit's reading ([`ModeQuotient::deposit_receiver`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separator {
    pub receiver: usize,
    pub phase: usize,
    pub word: Vec<usize>,
}

/// [definition] **The account of one present-silent direction** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Silence {
    /// Read by the admitted cycle at a later tick (`word.len()`, the cycle's word): retained.
    Heard(Separator),
    /// Silent to the whole admitted future, but a chart shared by every phase fails a square on
    /// it: retained, with the phase-family reading that separates it.
    SquareFails(Separator),
    /// In a learning aeon: silent to every exterior reading after every word, but a gain family's
    /// variation reads it, so its covector would not descend and a deposit would make it heard:
    /// retained, with the deposit's reading that separates it.
    Deposited(Separator),
    /// In the stable future kernel on which every square closes: released.
    Released,
}

/// [definition] **One present-silent direction** of the adapted basis, with its account.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SilentCoordinate {
    pub direction: Vec<Rat>,
    pub silence: Silence,
}

/// [definition] **An aeon's admission of deposit**: a frozen aeon admits none; a learning aeon
/// admits the declared material family's deposit (the loaded resonator), whose gain covectors read the
/// ring's state through the families' variations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Deposition {
    Frozen,
    Learning,
}

/// [definition] **Whether a gain family's covector descends to this chart** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GainDescent {
    /// The family's variation reads the state through the chart at every phase.
    Descends,
    /// The family's variation reads the released `direction` at pump phase `phase`: its covector
    /// changes along the release, which a learning aeon therefore retains.
    Reads { direction: Vec<Rat>, phase: usize },
}

// -------------------------------------------------------------------------------------------
// the quotient

/// [definition] **A loaded ring's mode quotient** under its admitted receiver family (module
/// header): the admitted future kernel by the period lift, the release by the one chart that closes
/// every phase's squares (in a learning aeon, with the deposit's readings admitted beside the
/// exterior ones), the descended operators, storage forms and variations, and the account of every
/// present-silent direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeQuotient {
    ring: usize,
    extent: usize,
    phases: usize,
    declared: usize,
    deposition: Deposition,
    requests: Vec<(usize, usize)>,
    exterior: usize,
    present: Vec<Vec<Rat>>,
    admitted: FaceMap,
    release: FaceMap,
    retention: Retention,
    sources: Vec<ExactRatMatrix>,
    feedthroughs: Vec<ExactRatMatrix>,
    storage: Vec<ExactRatMatrix>,
    variations: Vec<[Option<Variation>; GAIN_FAMILIES]>,
    descents: [GainDescent; GAIN_FAMILIES],
    hop: Rat,
    admittance: Rat,
    dissipation: ExactRatMatrix,
    silent: Vec<SilentCoordinate>,
}

/// Whether `x` lies in the span of the independent `basis`.
fn in_span(basis: &[Vec<Rat>], x: &[Rat]) -> Result<bool, HnnError> {
    if is_zero(x) {
        return Ok(true);
    }
    if basis.is_empty() {
        return Ok(false);
    }
    let mut rows = basis.to_vec();
    rows.push(x.to_vec());
    Ok(ExactRatMatrix::shaped(rows.len(), x.len(), rows)?.rank()? == basis.len())
}

fn receiver_reading(matrix: &ExactRatMatrix) -> Result<ReceiverReading, HnnError> {
    ReceiverReading::declared("mode receiver", matrix.clone())
        .map_err(|refusal| CompressionError::from(refusal).into())
}

/// The phase family: navigators `T_t`, every word; receivers `maps`.
fn phase_family(ring: &LoadedRing, maps: &[ExactRatMatrix]) -> Result<FaceMap, HnnError> {
    Ok(FaceMap::new(
        NavigatorFamily::declared(
            "the pump's phases",
            (0..ring.phases().len())
                .map(|phase| format!("T_{phase}"))
                .collect(),
            ring.phases().iter().map(|p| p.transport.clone()).collect(),
        )
        .map_err(CompressionError::from)?,
        maps.iter()
            .map(receiver_reading)
            .collect::<Result<Vec<_>, _>>()?,
    )?)
}

/// A declared reading's family: the requests, their maps and the face map they define.
struct Family<'a> {
    face: &'a FaceMap,
    requests: &'a [(usize, usize)],
    maps: &'a [ExactRatMatrix],
}

/// **A declared comparison's covector on one admitted reading**: receiver `receiver` (`0` the port,
/// `j + 1` the `j`-th declared) at word tick `tick`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadingCovector {
    pub receiver: usize,
    pub tick: usize,
    pub covector: Vec<Rat>,
}

/// [definition] **One tick of the descended block** (module header): its phase, the retained state
/// it leaves, the returned wave, the rate read from the port, and every term of its balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescendedTick {
    pub phase: usize,
    /// `q′ = T̄_t q + B̄_t e`.
    pub state: Vec<Rat>,
    /// `s′ = ρ̄_(0,t) q + D_t e`.
    pub output: Vec<Rat>,
    /// `ω = (Y/2)(e − s′)`.
    pub rate: Vec<Rat>,
    /// `½⟨q, Q̄_(t−1) q⟩`, the previous phase's storage (this phase's at the word's first tick).
    pub before: Rat,
    /// `½⟨q′, Q̄_t q′⟩`.
    pub after: Rat,
    /// `½⟨q, (Q̄_t − Q̄_(t−1)) q⟩`.
    pub pump: Rat,
    /// `(hY/4)(|e|² − |s′|²)`.
    pub port: Rat,
    /// `h⟨ω, D ω⟩`.
    pub dissipation: Rat,
}

impl DescendedTick {
    /// **The descended balance closes exactly**: `after − before = pump + port − dissipation`.
    pub fn closes(&self) -> bool {
        &self.after - &self.before == &self.pump + &self.port - &self.dissipation
    }
}

/// [definition] **The descended return of a declared comparison** (module header): the costates
/// `λ̄_t` on the retained chart (`λ_t = λ̄_t V` on the ring), the drive covectors `ē_t`, the solved
/// covectors `r̄_t` and each gain family's covector, `None` for a family that does not descend.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DescendedReturn {
    pub costates: Vec<Vec<Rat>>,
    pub drives: Vec<Vec<Rat>>,
    pub solved: Vec<Vec<Rat>>,
    pub gains: [Option<Rat>; GAIN_FAMILIES],
}

impl ModeQuotient {
    /// **The ring's mode quotient** under its port and the declared receivers, in an aeon that
    /// admits no deposit.
    pub fn of(ring: &LoadedRing, receivers: &[StateReceiver]) -> Result<Self, HnnError> {
        Self::build(ring, receivers, Deposition::Frozen)
    }

    /// **The ring's mode quotient in a learning aeon** (module header): the deposit's readings, the
    /// four families' variations at every phase, are admitted beside the port and the declared
    /// receivers, so every gain covector descends; a direction the frozen quotient releases but a
    /// variation reads is retained as [`Silence::Deposited`] with its separator.
    pub fn learning(ring: &LoadedRing, receivers: &[StateReceiver]) -> Result<Self, HnnError> {
        Self::build(ring, receivers, Deposition::Learning)
    }

    fn build(
        ring: &LoadedRing,
        receivers: &[StateReceiver],
        deposition: Deposition,
    ) -> Result<Self, HnnError> {
        let extent = ring.extent();
        let period = ring.phases().len();
        for receiver in receivers {
            if receiver.reading.columns() != extent || receiver.reading.rows() == 0 {
                return Err(HnnError::Shape {
                    what: "a state receiver reads the ring's state (u, w)",
                    expected: extent,
                    found: receiver.reading.columns(),
                });
            }
            if let Some(&phase) = receiver.phases.iter().find(|&&phase| phase >= period) {
                return Err(HnnError::Shape {
                    what: "a state receiver's phase (the pump's phases)",
                    expected: period,
                    found: phase,
                });
            }
        }
        // Every exterior reading `(r, t)`, phase-major; receiver 0 is the port.
        let mut requests = Vec::new();
        let mut maps: Vec<ExactRatMatrix> = Vec::new();
        for (phase, loaded) in ring.phases().iter().enumerate() {
            requests.push((0, phase));
            maps.push(loaded.reading.clone());
            for (index, receiver) in receivers.iter().enumerate() {
                if receiver.phases.contains(&phase) {
                    requests.push((index + 1, phase));
                    maps.push(receiver.reading.clone());
                }
            }
        }
        let exterior = requests.len();
        let lifted = requests
            .iter()
            .zip(&maps)
            .map(|(&(_, phase), map)| receiver_reading(&map.multiply(&ring.cycle(phase)?)?))
            .collect::<Result<Vec<_>, HnnError>>()?;
        let admitted = FaceMap::new(
            NavigatorFamily::declared(
                "the pump's period",
                vec!["T_P".into()],
                vec![ring.period()?],
            )
            .map_err(CompressionError::from)?,
            lifted,
        )?;
        let frozen = phase_family(ring, &maps)?;
        let frozen_released = frozen.kernel()?;
        let admitted_kernel = admitted.kernel()?;
        // K_rel ⊆ K_adm ⊆ N (`phase_kernel_le_lift`, `futureNull_le_ker_present`).
        let present_rows: Vec<Vec<Rat>> = requests
            .iter()
            .zip(&maps)
            .filter(|((_, phase), _)| *phase == 0)
            .flat_map(|(_, map)| map.to_rows())
            .collect();
        let present =
            ExactRatMatrix::shaped(present_rows.len(), extent, present_rows)?.kernel_basis()?;
        for direction in &frozen_released {
            if !in_span(&admitted_kernel, direction)? {
                return Err(HnnError::ModeQuotient {
                    ring: ring.ring(),
                    what: "the one-chart release leaves the admitted future kernel",
                });
            }
        }
        for direction in &admitted_kernel {
            if !in_span(&present, direction)? {
                return Err(HnnError::ModeQuotient {
                    ring: ring.ring(),
                    what: "the admitted future kernel leaves the present blind subspace",
                });
            }
        }
        // In a learning aeon the deposit reads every phase through the four variations
        // (`learning_chart_le_kernel`): receiver `1 + m + f` at phase `t`.
        let (release, all_requests, all_maps) = match deposition {
            Deposition::Frozen => (frozen.clone(), requests.clone(), maps.clone()),
            Deposition::Learning => {
                let (mut learned_requests, mut learned_maps) = (requests.clone(), maps.clone());
                for (phase, loaded) in ring.phases().iter().enumerate() {
                    for (family, variation) in loaded.variations.iter().enumerate() {
                        learned_requests.push((1 + receivers.len() + family, phase));
                        learned_maps.push(variation.state.clone());
                    }
                }
                (
                    phase_family(ring, &learned_maps)?,
                    learned_requests,
                    learned_maps,
                )
            }
        };
        let retention = release.quotient()?;
        let (retain, section) = (retention.retain(), retention.section());
        let sources = ring
            .phases()
            .iter()
            .map(|p| retain.multiply(&p.source))
            .collect::<Result<Vec<_>, _>>()?;
        let feedthroughs = ring
            .phases()
            .iter()
            .map(|p| p.feedthrough.clone())
            .collect();
        // The storage descends (`released_pair_storage_null`, `descended_form`): Q_t = Vᵀ Q̄_t V.
        let storage = ring
            .phases()
            .iter()
            .map(|p| {
                let descended = section
                    .transpose()?
                    .multiply(&p.storage)?
                    .multiply(section)?;
                if retain.transpose()?.multiply(&descended)?.multiply(retain)? != p.storage {
                    return Err(HnnError::ModeQuotient {
                        ring: ring.ring(),
                        what: "the storage form reads a released direction",
                    });
                }
                Ok(descended)
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        // Each variation descends exactly when it reads nothing released: F = (F σ) V.
        let mut variations = Vec::with_capacity(period);
        for loaded in ring.phases() {
            let mut descended: [Option<Variation>; GAIN_FAMILIES] = Default::default();
            for (family, variation) in loaded.variations.iter().enumerate() {
                let state = variation.state.multiply(section)?;
                if state.multiply(retain)? == variation.state {
                    descended[family] = Some(Variation {
                        state,
                        drive: variation.drive.clone(),
                    });
                }
            }
            variations.push(descended);
        }
        let released = release.kernel()?;
        let mut descents: [GainDescent; GAIN_FAMILIES] =
            std::array::from_fn(|_| GainDescent::Descends);
        for (family, descent) in descents.iter_mut().enumerate() {
            'phases: for (phase, loaded) in ring.phases().iter().enumerate() {
                for direction in &released {
                    if !is_zero(&loaded.variations[family].state.apply(direction)?) {
                        *descent = GainDescent::Reads {
                            direction: direction.clone(),
                            phase,
                        };
                        break 'phases;
                    }
                }
            }
        }
        if deposition == Deposition::Learning
            && descents.iter().any(|d| *d != GainDescent::Descends)
        {
            return Err(HnnError::ModeQuotient {
                ring: ring.ring(),
                what: "a learning chart releases a direction a variation reads",
            });
        }
        let mut quotient = Self {
            ring: ring.ring(),
            extent,
            phases: period,
            declared: receivers.len(),
            deposition,
            requests: all_requests,
            exterior,
            present,
            admitted,
            release,
            retention,
            sources,
            feedthroughs,
            storage,
            variations,
            descents,
            hop: ring.hop.clone(),
            admittance: ring.admittance.clone(),
            dissipation: ring.dissipation.clone(),
            silent: Vec::new(),
        };
        let exterior_family = Family {
            face: &frozen,
            requests: &requests,
            maps: &maps,
        };
        let learned_family = Family {
            face: &quotient.release,
            requests: &quotient.requests,
            maps: &all_maps,
        };
        let silent = quotient.account(
            ring,
            &exterior_family,
            &learned_family,
            released,
            frozen_released,
            admitted_kernel,
        )?;
        quotient.silent = silent;
        Ok(quotient)
    }

    /// The adapted basis of `N` over `K_rel ⊆ K_adm` (in a learning aeon, over
    /// `K_learn ⊆ K_rel ⊆ K_adm`), each direction with its account.
    fn account(
        &self,
        ring: &LoadedRing,
        exterior: &Family,
        learned: &Family,
        released: Vec<Vec<Rat>>,
        frozen_released: Vec<Vec<Rat>>,
        admitted_kernel: Vec<Vec<Rat>>,
    ) -> Result<Vec<SilentCoordinate>, HnnError> {
        let mut chosen: Vec<Vec<Rat>> = Vec::new();
        let mut silent = Vec::new();
        for direction in released {
            chosen.push(direction.clone());
            silent.push(SilentCoordinate {
                direction,
                silence: Silence::Released,
            });
        }
        for direction in frozen_released {
            if !in_span(&chosen, &direction)? {
                let separator = self.phase_separator(ring, learned, &direction)?;
                chosen.push(direction.clone());
                silent.push(SilentCoordinate {
                    direction,
                    silence: Silence::Deposited(separator),
                });
            }
        }
        for direction in admitted_kernel {
            if !in_span(&chosen, &direction)? {
                let separator = self.phase_separator(ring, exterior, &direction)?;
                chosen.push(direction.clone());
                silent.push(SilentCoordinate {
                    direction,
                    silence: Silence::SquareFails(separator),
                });
            }
        }
        for direction in self.present.clone() {
            if !in_span(&chosen, &direction)? {
                let separator = self.cycle_separator(ring, exterior, &direction)?;
                chosen.push(direction.clone());
                silent.push(SilentCoordinate {
                    direction,
                    silence: Silence::Heard(separator),
                });
            }
        }
        Ok(silent)
    }

    /// The first tick of the admitted cycle, and its first receiver, that read `x`: within
    /// `P (m + 1)` ticks, `m` the lift's stable horizon, when `x ∉ K_adm`.
    fn cycle_separator(
        &self,
        ring: &LoadedRing,
        family: &Family,
        x: &[Rat],
    ) -> Result<Separator, HnnError> {
        let mut state = x.to_vec();
        for tick in 0..self.phases * (self.admitted.stable_at() + 1) {
            let phase = tick % self.phases;
            for (&(receiver, at), map) in family.requests.iter().zip(family.maps) {
                if at == phase && !is_zero(&map.apply(&state)?) {
                    return Ok(Separator {
                        receiver,
                        phase,
                        word: (0..tick).rev().map(|s| s % self.phases).collect(),
                    });
                }
            }
            state = ring.phases()[phase].transport.apply(&state)?;
        }
        Err(HnnError::ModeQuotient {
            ring: self.ring,
            what: "a direction outside the admitted kernel has no admitted reading",
        })
    }

    /// The shortest phase-family word and reading that separate `x` outside the family's kernel:
    /// from the first horizon `n` with `x ∉ B_n`, some letter carries `x` out of `B_(n−1)`, down
    /// to a reading.
    fn phase_separator(
        &self,
        ring: &LoadedRing,
        family: &Family,
        x: &[Rat],
    ) -> Result<Separator, HnnError> {
        let blinds = (0..=family.face.stable_at())
            .map(|horizon| family.face.blind(horizon))
            .collect::<Result<Vec<_>, _>>()?;
        let mut level = None;
        for (horizon, blind) in blinds.iter().enumerate() {
            if !in_span(blind, x)? {
                level = Some(horizon);
                break;
            }
        }
        let mut level = level.ok_or(HnnError::ModeQuotient {
            ring: self.ring,
            what: "a direction outside the release lies in every blind subspace",
        })?;
        let mut state = x.to_vec();
        let mut acting = Vec::new();
        loop {
            for (&(receiver, phase), map) in family.requests.iter().zip(family.maps) {
                if !is_zero(&map.apply(&state)?) {
                    acting.reverse();
                    return Ok(Separator {
                        receiver,
                        phase,
                        word: acting,
                    });
                }
            }
            if level == 0 {
                return Err(HnnError::ModeQuotient {
                    ring: self.ring,
                    what: "a direction outside the present blind subspace has no reading",
                });
            }
            let below = &blinds[level - 1];
            let mut next = None;
            for (letter, phase) in ring.phases().iter().enumerate() {
                let carried = phase.transport.apply(&state)?;
                if !in_span(below, &carried)? {
                    next = Some((letter, carried));
                    break;
                }
            }
            let (letter, carried) = next.ok_or(HnnError::ModeQuotient {
                ring: self.ring,
                what: "no phase carries a direction out of the next blind subspace",
            })?;
            acting.push(letter);
            state = carried;
            level -= 1;
        }
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `2n`, the state's extent.
    pub fn extent(&self) -> usize {
        self.extent
    }

    /// The pump phases.
    pub fn phases(&self) -> usize {
        self.phases
    }

    /// The aeon's admission of deposit this quotient was formed for.
    pub fn deposition(&self) -> Deposition {
        self.deposition
    }

    /// **The retention chart** `V`, of full row rank, `ker V = K_rel` (`K_learn` in a learning
    /// aeon).
    pub fn retain(&self) -> &ExactRatMatrix {
        self.retention.retain()
    }

    /// **A section** `σ` of the chart, `V σ = 1`.
    pub fn section(&self) -> &ExactRatMatrix {
        self.retention.section()
    }

    /// `rank V`.
    pub fn retained_rank(&self) -> usize {
        self.retention.extent()
    }

    /// `dim ker V`.
    pub fn released_rank(&self) -> usize {
        self.extent - self.retention.extent()
    }

    /// A basis of `ker V`, the directions released.
    pub fn released(&self) -> Result<Vec<Vec<Rat>>, HnnError> {
        Ok(self.release.kernel()?)
    }

    /// A basis of `N = ker F_now`, the directions the present exterior family does not read.
    pub fn present_silent(&self) -> &[Vec<Rat>] {
        &self.present
    }

    /// **The period lift**: [`FaceMap`] on `{T_P}` and the phase-offset exterior receivers
    /// `ρ_(r,k) Φ(k)`, in the order of [`ModeQuotient::exterior_requests`]; its kernel is `K_adm`.
    pub fn admitted(&self) -> &FaceMap {
        &self.admitted
    }

    /// **The phase family** the chart comes from: [`FaceMap`] on `{T_t}` and the readings of
    /// [`ModeQuotient::requests`]; its kernel is `ker V`.
    pub fn release(&self) -> &FaceMap {
        &self.release
    }

    /// The readings `(receiver, phase)`: the exterior ones phase-major (receiver `0` the port), then
    /// in a learning aeon the deposit's, receiver `1 + m + f` for family `f`.
    pub fn requests(&self) -> &[(usize, usize)] {
        &self.requests
    }

    /// The exterior readings `(receiver, phase)`, the port's and the declared receivers', in the
    /// order of [`ModeQuotient::admitted`]'s receivers.
    pub fn exterior_requests(&self) -> &[(usize, usize)] {
        &self.requests[..self.exterior]
    }

    /// The deposit's receiver for gain family `f` in a learning aeon.
    pub fn deposit_receiver(&self, family: usize) -> Option<usize> {
        (self.deposition == Deposition::Learning && family < GAIN_FAMILIES)
            .then_some(1 + self.declared + family)
    }

    /// `T̄_t`, with `V T_t = T̄_t V`.
    pub fn transport(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.retention.navigator(phase)
    }

    /// `B̄_t = V B_t`.
    pub fn source(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.sources.get(phase)
    }

    /// `D_t`, unchanged by the descent.
    pub fn feedthrough(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.feedthroughs.get(phase)
    }

    /// `Q̄_t = σᵀ Q_t σ`, with `Q_t = Vᵀ Q̄_t V`: the descended storage form.
    pub fn storage(&self, phase: usize) -> Option<&ExactRatMatrix> {
        self.storage.get(phase)
    }

    /// Gain family `f`'s variation at pump phase `t` on the chart, `φ = F̄ q + H e` with
    /// `F = F̄ V`; `None` when the family does not descend.
    pub fn variation(&self, phase: usize, family: usize) -> Option<&Variation> {
        self.variations.get(phase)?.get(family)?.as_ref()
    }

    /// Whether gain family `f`'s covector descends to this chart, or the released direction it
    /// reads.
    pub fn gain_descent(&self, family: usize) -> Option<&GainDescent> {
        self.descents.get(family)
    }

    /// `ρ̄_(r,t)`, with `ρ_(r,t) = ρ̄_(r,t) V`, where receiver `r` reads at phase `t`.
    pub fn reading(&self, receiver: usize, phase: usize) -> Option<&ExactRatMatrix> {
        let index = self
            .requests
            .iter()
            .position(|&request| request == (receiver, phase))?;
        self.retention.reading(index)
    }

    /// The account of every present-silent direction, in the adapted basis.
    pub fn silent(&self) -> &[SilentCoordinate] {
        &self.silent
    }

    /// `V x`.
    pub fn retained(&self, state: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        Ok(self.retention.retained(state)?)
    }

    fn check(&self, what: &'static str, expected: usize, found: usize) -> Result<(), HnnError> {
        if expected == found {
            Ok(())
        } else {
            Err(HnnError::Shape {
                what,
                expected,
                found,
            })
        }
    }

    fn descended<'a>(
        &self,
        matrix: Option<&'a ExactRatMatrix>,
    ) -> Result<&'a ExactRatMatrix, HnnError> {
        matrix.ok_or(HnnError::ModeQuotient {
            ring: self.ring,
            what: "every phase descends and the port reads at every phase",
        })
    }

    /// **One tick of the descended block** at word tick `t` (module header): from the retained
    /// state `q` and the drive `e`, `q′ = T̄_t q + B̄_t e`, `s′ = ρ̄_(0,t) q + D_t e`, the rate
    /// `ω = (Y/2)(e − s′)`, and the balance on the descended storage forms (Lean
    /// `descended_balance`).
    pub fn tick(
        &self,
        tick: usize,
        retained: &[Rat],
        drive: &[Rat],
    ) -> Result<DescendedTick, HnnError> {
        self.check(
            "a retained state (the chart's rank)",
            self.retained_rank(),
            retained.len(),
        )?;
        let phase = tick % self.phases;
        let previous = if tick == 0 {
            phase
        } else {
            (tick - 1) % self.phases
        };
        let feedthrough = &self.feedthroughs[phase];
        self.check(
            "a drive (the ring's realified width)",
            feedthrough.columns(),
            drive.len(),
        )?;
        let port = self.descended(self.reading(0, phase))?;
        let output = add(&port.apply(retained)?, &feedthrough.apply(drive)?);
        let state = add(
            &self.descended(self.transport(phase))?.apply(retained)?,
            &self.sources[phase].apply(drive)?,
        );
        let rate = scale(&(&self.admittance / integer(2)), &sub(drive, &output));
        let half = |form: &ExactRatMatrix, q: &[Rat]| -> Result<Rat, HnnError> {
            Ok(dot(q, &form.apply(q)?) / integer(2))
        };
        let before = half(&self.storage[previous], retained)?;
        let now = half(&self.storage[phase], retained)?;
        let after = half(&self.storage[phase], &state)?;
        let port_work =
            &self.hop * &self.admittance / integer(4) * (dot(drive, drive) - dot(&output, &output));
        let dissipation = &self.hop * dot(&rate, &self.dissipation.apply(&rate)?);
        Ok(DescendedTick {
            phase,
            pump: &now - &before,
            before,
            after,
            port: port_work,
            dissipation,
            state,
            output,
            rate,
        })
    }

    /// **The descended block's ticks** from a retained state `q` on the drives `e_t`, word tick `t`
    /// at phase `t mod P`.
    pub fn ticks(
        &self,
        retained: &[Rat],
        drives: &[Vec<Rat>],
    ) -> Result<Vec<DescendedTick>, HnnError> {
        let mut state = retained.to_vec();
        let mut ticks = Vec::with_capacity(drives.len());
        for (tick, drive) in drives.iter().enumerate() {
            let stepped = self.tick(tick, &state, drive)?;
            state = stepped.state.clone();
            ticks.push(stepped);
        }
        Ok(ticks)
    }

    /// **The descended ring's run** from a retained state `q` on the drives `e_t`: the returned
    /// waves `s′_t = ρ̄_(0,t) q_t + D_t e_t`, with `q_(t+1) = T̄_t q_t + B̄_t e_t` (Lean
    /// `descended_run_reads`).
    pub fn run(&self, retained: &[Rat], drives: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, HnnError> {
        Ok(self
            .ticks(retained, drives)?
            .into_iter()
            .map(|tick| tick.output)
            .collect())
    }

    /// **The descended return of a declared comparison** (module header; Lean
    /// `descended_costate`, `descended_drive_covector`, `descended_gain`): from the retained state
    /// `q_0`, the drives and the comparison's covectors on the admitted exterior readings, backward
    /// from the word's end (`λ̄_N = 0`):
    ///
    /// ```text
    /// ē_t = B̄_tᵀ λ̄_(t+1) + D_tᵀ s̄_t        r̄_t = (ē_t − s̄_t)/h
    /// λ̄_t = T̄_tᵀ λ̄_(t+1) + Σ_r ρ̄_(r,t)ᵀ ȳ_(r,t)
    /// G_f = Σ_t ⟨r̄_t, F̄_(f,t) q_t + H_(f,t) e_t⟩
    /// ```
    ///
    /// A covector on a reading the family does not admit is refused.
    pub fn pull_back(
        &self,
        retained: &[Rat],
        drives: &[Vec<Rat>],
        covectors: &[ReadingCovector],
    ) -> Result<DescendedReturn, HnnError> {
        let ticks = drives.len();
        let rank = self.retained_rank();
        for covector in covectors {
            let reading = if covector.receiver <= self.declared && covector.tick < ticks {
                self.reading(covector.receiver, covector.tick % self.phases)
            } else {
                None
            };
            let reading = reading.ok_or(HnnError::ModeQuotient {
                ring: self.ring,
                what: "a comparison's covector lies on an admitted exterior reading of the word",
            })?;
            self.check(
                "a comparison's covector (its reading's extent)",
                reading.rows(),
                covector.covector.len(),
            )?;
        }
        let mut states = vec![retained.to_vec()];
        for tick in 0..ticks {
            let stepped = self.tick(tick, &states[tick], &drives[tick])?;
            states.push(stepped.state);
        }
        let h_inverse = Rat::one() / &self.hop;
        let mut costate = zeros(rank);
        let (mut costates, mut drive_bars, mut solved) = (
            vec![Vec::new(); ticks],
            vec![Vec::new(); ticks],
            vec![Vec::new(); ticks],
        );
        let mut gains: [Option<Rat>; GAIN_FAMILIES] = std::array::from_fn(|family| {
            (self.descents[family] == GainDescent::Descends).then(Rat::zero)
        });
        for tick in (0..ticks).rev() {
            let phase = tick % self.phases;
            let width = self.feedthroughs[phase].rows();
            let mut port_bar = zeros(width);
            let mut next = self
                .descended(self.transport(phase))?
                .transpose()?
                .apply(&costate)?;
            for covector in covectors.iter().filter(|c| c.tick == tick) {
                let reading = self.descended(self.reading(covector.receiver, phase))?;
                next = add(&next, &reading.transpose()?.apply(&covector.covector)?);
                if covector.receiver == 0 {
                    port_bar = add(&port_bar, &covector.covector);
                }
            }
            let drive_bar = add(
                &self.sources[phase].transpose()?.apply(&costate)?,
                &self.feedthroughs[phase].transpose()?.apply(&port_bar)?,
            );
            let solve = scale(&h_inverse, &sub(&drive_bar, &port_bar));
            for (family, gain) in gains.iter_mut().enumerate() {
                if let (Some(gain), Some(variation)) = (gain, self.variation(phase, family)) {
                    *gain += dot(&solve, &variation.apply(&states[tick], &drives[tick])?);
                }
            }
            costate = next;
            costates[tick] = costate.clone();
            drive_bars[tick] = drive_bar;
            solved[tick] = solve;
        }
        Ok(DescendedReturn {
            costates,
            drives: drive_bars,
            solved,
            gains,
        })
    }
}

impl SilentCoordinate {
    /// Whether this direction is released.
    pub fn released(&self) -> bool {
        matches!(self.silence, Silence::Released)
    }
}
