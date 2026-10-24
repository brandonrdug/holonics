//! **The moment tower: modes driven by the encoding, read through rectifying contacts, level over
//! level** (#405, #404).
//!
//! [definition; agent-inferred, October 23] Why it is built. On GSM8K the receiving tree, the
//! passage and the node lock code 1.64 bits a character, and their samples babble. The
//! mathematics thread's field reading (record
//! `2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM…`) fits that lens a floor
//! of about 1.2 bits a byte that its learning approaches and cannot pass, and answer prose sits on
//! it after a quarter of the passage. A count of exact contexts cannot generalize from one context
//! to a similar one; sharpening its draw only loops. The keyed modes (`hnn::keyed_modes`), 32
//! diagonal modes read linearly at the cell grain, added nothing: a cell's two bits name no class
//! of the codec, and a linear read takes no conjunction. The mathematics thread's §2 names what a
//! selective state-space model does instead: diagonal transports, with the conjunction taken by a
//! nonlinear read between levels, the tower. This owner is that tower at the codec's own classes.
//!
//! ```text
//! encoding   x⁰_t = E(u_t)                                   the class's face, located
//! level ℓ    h_t = λ ⊙ h_(t−1) + γ ⊙ B x^ℓ_t                 N complex modes: λ the navigator's turn
//!                                                            and boost, B the push (the source moment),
//!                                                            γ = √(1 − |λ|²) its passive scale
//!            r_t = Re(C h_t)                                 the modes' receiving face
//!            r̂_t = r_t / ‖r_t‖_rms                           read as a ratio to its own power
//!            v_t = max(W₁ r̂_t + b₁, 0)                       rectifying contacts (they conduct one way)
//!            x^(ℓ+1)_t = x^ℓ_t + W₂ v_t + b₂
//! face       z_t = U x^L_t + c,   p̂_t(a) = 2^(z_a) / Σ_b 2^(z_b)
//! covector   δz = p̂_t − [· = u_(t+1)]                         the comparison's descent covector, in bits
//! adjoint    G_h(t) = (Cᵀδr)⁻ + conj(λ) G_h(t+1)              the reverse scan inside one section
//!            G_λ = Σ_t conj(h_(t−1)) G_h(t) − (λ/γ) Σ_t Re(conj(G_h(t)) B x_t)
//!            G_B = Σ_t γ G_h(t) x^ℓ_tᵀ
//! deposit    θ ← θ − 2^(−k) m / (√v + 2^(−32))               m, v the covector's first and second moments
//!                                                            over sections (`1 − 2^(−3)`, `1 − 2^(−8)`);
//!                                                            a move in its chart (ln(1 − |λ|), arg λ)
//! certificate the section reread from its opening states under the deposit codes strictly fewer
//!            bits (an exact comparison of the products of its faces); else the step halves, until
//!            it is certified or has released below every family's grain (then nothing is
//!            deposited)
//! ```
//!
//! **Passivity.** With `γ = √(1 − |λ|²)` a mode's state under a unit white push keeps unit
//! power whatever its decay, and under any push `|h| ≤ γ/(1 − |λ|) max|B x| = √((1 + |λ|)/(1 − |λ|))
//! max|B x| ≤ 2^(13/2) max|B x|` inside the margin. Without it, a decay moved toward the margin
//! raised the state's gain as `1/(1 − |λ|)` (measured: five-fold over nine sections, then past the
//! contact's carrier in the next).
//!
//! **The gated mode** ([`TowerDeclaration::gated`], agent-inferred, October 23). A mode's decay
//! is keyed by the face it receives: the level's input opens a gate `r_t = 1/(1 + 2^(−q_t))`,
//! `q_t = W_g x^ℓ_t + b_g`, and the move at that cell keeps its turn while its modulus is the
//! founded one raised by the gate, `λ_t = |λ|^(c r_t) λ/|λ|`, `γ_t = √(1 − |λ_t|²)`, `c = 2`. A
//! closed gate (`r → 0`) holds the mode (`|λ_t| → 1`, so `γ_t → 0` and the push is not admitted:
//! the mode is dormant); an open one (`r → 1`) releases it at `|λ|²` a cell and admits the push. The
//! gate's material opens at zero, so `r = ½` and the gated tower opens on the ungated one (to the
//! grain of `log₂` and `2^x`). This is the classical selective recurrence (the RG-LRU's recurrence
//! gate). Its adjoint, with `ℓ = log₂|λ|`, `u = λ/|λ|`, `ρ_t = |λ_t|`:
//!
//! ```text
//! G_h(t)  = (Cᵀδr)⁻ + conj(λ_(t+1)) G_h(t+1)
//! G_ρ(t)  = Re(conj(u) conj(h_(t−1)) G_h(t)) − (ρ_t/γ_t) Re(conj(G_h(t)) B x_t)
//! δq_t    = G_ρ(t) · c ρ_t ℓ (ln 2)² r_t (1 − r_t)
//! G_|λ|   = Σ_t G_ρ(t) c r_t ρ_t/|λ|,      G_φ = Σ_t Im(conj(λ_t) conj(h_(t−1)) G_h(t))
//! G_λ     = u G_|λ| + i u G_φ/|λ|           (the Cartesian covector, so the move chart is shared)
//! ```
//!
//! `ρ_t` is held at the margin `1 − 2^(−12)`, where its covector reaches neither the gate nor `|λ|`;
//! under that hold the passivity bound below holds cell by cell, `|h_t| ≤ ρ_t |h_(t−1)| + γ_t |Bx_t|
//! ≤ √((1 + ρ_max)/(1 − ρ_max)) max|Bx|`, since `γ/(1 − ρ)` increases with `ρ`.
//!
//! **The turned mode** ([`TowerDeclaration::turned`], agent-inferred, October 23). A gated mode
//! whose turn is keyed too: the arriving symbol turns it by `s_t = 2^(−⌈log₂ w⌉) (W_φ x^ℓ_t + b_φ)`
//! half turns on `2^(−16)` (the drive read as its mean over the width), `λ_t = ρ_t u e^(iπ s_t)`, so
//! a mode can carry a residue as its accumulated phase (on the units of `ℤ/q` the index chart turns
//! a product into a sum of turns). `e^(iπ s)` is composed from the dyadic ladder `e^(iπ/2^j)` by the
//! binary digits of `s` modulo the full turn, the half turn `π` from Machin's series. The turn's
//! material opens at zero, so a turned tower opens on its gated twin. Its covector is the turn's
//! share of the move's, `G_s(t) = π 2^(−⌈log₂ w⌉) Re(conj(i λ_t) G_λ(t))`, to `W_φ` and `b_φ` (the
//! code's difference agrees, tested). The passage credit does not carry it (a typed refusal).
//!
//! **The pumped mode** ([`TowerDeclaration::pumped`], agent-inferred, October 23). A turned mode
//! that the arriving symbol also pumps: its move is the parametron's (`holon::parametron`), a turn
//! plus a reflection,
//!
//! ```text
//! h_t = α_t h_(t−1) + β_t conj(h_(t−1)) + γ_t B x_t
//! α_t = ρ_t (1 − |κ_t|) U_t,   U_t = u e^(iπ s_t)                 the turned unit
//! β_t = ρ_t κ_t P_t,           P_t = e^(iπ p_t)                   the pump: depth κ, axis at π p/2
//! κ_t = 2 r_t − 1,  r_t = 1/(1 + 2^(−(W_κ x + b_κ))),   p_t = 2^(−⌈log₂ w⌉) (W_ψ x + b_ψ)
//! ```
//!
//! `β conj(h)` reflects the state across the pump's axis (a pump reads the doubled phase). As a
//! real `2×2` move it has determinant `ρ²(1 − 2|κ|)` and trace `2ρ(1 − |κ|) cos θ_U`: it turns
//! (elliptic) while `(1 − |κ|)² cos² θ_U < 1 − 2|κ|`, and past that bifurcation its in-phase axis
//! boosts while the quadrature is shed (hyperbolic: the mode settles on one of two sheets), with a
//! shear on the edge: the Swing's three kinds, keyed cell by cell by the symbol. Why: a residue is
//! a discrete phase; the turned mode carried it as an angle whose neighbours look alike (the
//! turned tower's sums slipped one step on their units), and a lock gives it somewhere to sit.
//! Passivity holds as before: the move's real-linear norm is `|α| + |β| = ρ_t`, so
//! `|h_t| ≤ ρ_t |h_(t−1)| + γ_t |B x_t|` with the same `γ_t = √(1 − ρ_t²)`. The pump's material
//! opens at zero (`κ = 0`, `β = 0`), so a pumped tower opens on its turned twin. The adjoint carries
//! `conj(α) G + β conj(G)` back a cell, and with `G_α = conj(h_(t−1)) G_h(t)`, `G_β = h_(t−1) G_h(t)`:
//!
//! ```text
//! G_ρ(t)  = Re(conj(α/ρ) G_α) + Re(conj(β/ρ) G_β) − (ρ_t/γ_t) Re(conj(G_h(t)) B x_t)
//! δq_κ    = (−sgn(κ) Re(conj(ρU) G_α) + Re(conj(ρP) G_β)) · 2 ln 2 r (1 − r)
//! G_p     = π Re(conj(i β) G_β),   G_s = π Re(conj(i α) G_α)
//! ```
//!
//! (`sgn 0 = 0`, the symmetric difference's reading at the opening; the code's difference agrees,
//! tested). The passage credit does not carry it.
//!
//! **The contacts read a ratio.** A contact conducts on the direction of the modes' face, not its
//! power: `r̂ = r / ‖r‖_rms`, with the adjoint `∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms`. Read on its
//! power, the drive followed the face's scale (some 50 units on the 1,000-problem passage), a step
//! of the contacts moved it by tens of units, and the first level's contacts stopped conducting: 251
//! of 256 changed no weight in the second pass, so no covector reached its modes (measured).
//!
//! **The read's carrier.** The ratio read makes the forward blind to the read's scale `‖C‖`, so
//! the covector of `C` is orthogonal to `C` and every normalized step lengthens it (the step's
//! effective rate on the read falls as `1/‖C‖`). The raw read `r = Re(C h)` is therefore carried in
//! 64 bits before the ratio is taken. Measured: on all 6,726 GSM8K problems the second level's
//! largest `‖r‖_rms` grew from 739 to 1,795 face units over passes 3 and 4, and a held-out read
//! after pass 4 passed the 32-bit carrier (a typed refusal).
//!
//! **The mode face's carrier.** Passivity bounds a mode by its drive: `|h_t| ≤ ρ|h_(t−1)| + γ|B x_t|`
//! with `γ = √(1 − ρ²)` gives `|h| ≤ √((1 + ρ)/(1 − ρ)) max|B x|`, about `90.5 max|B x|` at the
//! margin `ρ = 1 − 2^(−12)`. A face carried in 32 bits holds `2^15` face units, which a mode at the
//! margin passes once `|B x|` passes about 362, a reach the law admits; the face (`h` released to
//! `2^(−16)`) is therefore carried in `i64`, and the read's and the read covector's sums widen to
//! `i128` where its terms need it. Measured: with wrong attempts read on side forks
//! (`solenoidal_alpha::complete_language::tower_train`), the second level's face reached
//! 1,517,888,300 numerators (23,161 face units) at the fifth pass's section 66, 40 times the most
//! the plain tower's reached in its whole training (38,222,409), and then passed `2^31` (a typed
//! refusal).
//!
//! **The pair contact** ([`ContactLaw::Pair`], agent-inferred with the mathematics thread, October
//! 24). The face law (record `2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_…`) reads every
//! section's located relation through one pair contact `W(x̄ ⊗ ȳ)`, `x̄ = (x, 1)`: a constant block,
//! two one-sided blocks (copy, agreement, codomain), an additive block and a bilinear one, with the
//! slip `δ = q(r) − r̂` as its check and its covector. A rectifier takes a conjunction only through
//! its kink; the pair contact takes it as the product of two drives read off the same face, so a
//! drive keyed by a held mode can gate a drive keyed by a fast one:
//!
//! ```text
//! v_t            = (W_a r̂_t + b_a) ⊙ (W_b r̂_t + b_b)
//! δ(W_a r̂ + b_a) = δv ⊙ (W_b r̂ + b_b),      δ(W_b r̂ + b_b) = δv ⊙ (W_a r̂ + b_a)
//! ```
//!
//! The second drive opens at `W_b = 0`, `b_b = 1`, so the contact opens one-sided
//! (`v = W_a r̂ + b_a`, no kink) and the bilinear block is learned from there; the first drive is
//! founded as the rectifier's. The foil [`ContactLaw::PairLinear`] holds the bilinear block at
//! zero, `v = (W_a r̂ + b_a) b_b + b_a (W_b r̂)`: the same material and the same opening with every
//! block but the product, so what the product carries is read against it.
//!
//! **What a section holds.** The forward's temporaries of its own cells, for the reverse scan, and
//! the streams' opening states, for the reread. They are released when the section closes (the
//! Athena alpha plan's §A2.4: the reverse pairs the forward prefix operands with the backward
//! covectors, inside the section only). What continues is the material and each stream's mode state.
//!
//! **The passage credit** ([`LevelCredit`], agent-inferred, October 23). A section's reverse scan
//! starts at zero at its end and its covector stopped at its opening, so a parameter learned only
//! from what the last `T` bytes did, while a mode near the margin holds about `2^12` (GPT-6's
//! review). A learner's streams now carry, beside each mode's state, the state's derivative by the
//! level's own recurrence families, moved forward cell by cell as phase-carried moments; at a
//! section's opening the covector reaching the carried state, `a = conj(λ_0) G_h(0)`, meets them.
//! On one level, two halves of a passage with the second opening on the first's credit give the
//! whole passage's covector in every recurrence family, to the moments' release (tested). The
//! credit holds the level's input, and the encoding, as given: what reaches a level from the levels
//! below stays inside the section. The certificate still rereads the section from its opening, so
//! the certified step is descent on the section under the passage's direction.
//!
//! **Exact integers, grains declared.** Every quantity is an integer numerator on a declared dyadic
//! grain: a face (`x`, `r`, `v`, `z`) on `2^(−16)`, the material on `2^(−24)`, the moves `λ` on
//! `2^(−30)` with `|λ| ≤ 1 − 2^(−12)`, a mode's state on `2^(−24)`, a covector on `2^(−24)` in
//! `i64` (a slow mode's covector accumulates over a section's reverse scan; measured, it outgrew
//! `i32` in the second pass on 1,000 GSM8K problems). Each
//! product's remainder below its grain is released to the nearest numerator. A sum is checked
//! against its carrier before it is formed: an `i64` sum widens to `i128` where its terms could
//! reach `2^62`, and a released value that outgrows its carrier is a typed refusal, never a wrap.
//! `2^(z)` is the dyadic square-root navigator's face ([`Exponential`]). Integer sums are
//! associative, so the streams' covectors summed in any order give the same bits.
//!
//! **Modality.** The tower reads classes of a declared alphabet and nothing else. A text, image,
//! acoustic or motor boundary chart supplies the classes (bytes, for text).
//!
//! **Not claimed.** The nonlinearity of the completed model is in the state (a parametron's lock);
//! without the pumped mode it sits between levels, the classical selective model's place, and with
//! it the lock is one symbol-keyed reflection a cell, not yet a Floquet-certified pump. The certified
//! step is descent on its own section, not on the passage.
use crate::hnn::keyed_modes::{dyadic_turn, ln2_face, release, Exponential};
use crate::hnn::passage::log2_face;
use num_bigint::BigUint;
use rayon::prelude::*;

pub mod duplex;

/// A face's grain, `2^(−16)`.
pub const FACE_BITS: u32 = 16;
/// The material's grain, `2^(−24)`.
pub const MATERIAL_BITS: u32 = 24;
/// The moves' grain, `2^(−30)`.
pub const MOVE_BITS: u32 = 30;
/// A mode's state grain, `2^(−24)`.
pub const STATE_BITS: u32 = 24;
/// A covector's grain, `2^(−24)`.
pub const COVECTOR_BITS: u32 = 24;
/// The deposit's covector grain, `2^(−32)`, and its ε.
pub const STEP_BITS: u32 = 32;
/// The moves' margin inside the unit disk, `|λ| ≤ 1 − 2^(−12)`: a mode's memory reaches some
/// 4,096 classes (agent-inferred: past a GSM8K problem of some 520 bytes, inside the passage).
pub const MARGIN: u32 = 12;
/// A code reading's grain, `2^(−20)` bits.
pub const READ_BITS: u32 = 20;
/// The first moment's rate, `2^(−3)`, and the second's, `2^(−8)` (agent-inferred: the classical
/// 0.9 and 0.999 read as dyadic rates; the second at `2^(−8)` so a pass of a few hundred sections
/// renews it).
const FIRST_RATE: u32 = 3;
const SECOND_RATE: u32 = 8;
const UNIT_BITS: u32 = 62;

/// Refusals of the tower's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TowerError {
    #[error("tower refused: {0}")]
    Refused(&'static str),
}

type Result<T> = std::result::Result<T, TowerError>;

fn refuse<T>(why: &'static str) -> Result<T> {
    Err(TowerError::Refused(why))
}

fn fit32(x: i128, what: &'static str) -> Result<i32> {
    i32::try_from(x).map_err(|_| TowerError::Refused(what))
}

fn fit64(x: i128) -> Result<i64> {
    i64::try_from(x).map_err(|_| TowerError::Refused("a released value outgrew its 64-bit carrier"))
}

/// [definition; agent-inferred] **The tower's declared law**: an alphabet of `A` classes, a face
/// width `d`, `N` complex modes and `f` rectifying contacts a level, and `L` levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TowerDeclaration {
    pub alphabet: usize,
    pub width: usize,
    pub modes: usize,
    pub contacts: usize,
    pub levels: usize,
    /// Whether each mode's decay is keyed by its input (the gated mode, in the module's law).
    pub gated: bool,
    /// Whether each gated mode's turn is keyed by its input too (the turned mode): the arriving
    /// symbol turns the mode, so a mode can carry a residue as its phase.
    pub turned: bool,
    /// Whether each turned mode is pumped too (the pumped mode): the arriving symbol keys a
    /// reflection mixed into the move, so a mode's phase can lock on one of two sheets.
    pub pumped: bool,
    /// How a level's contacts conduct: rectifying, or the pair contact or its linear foil.
    pub contact: ContactLaw,
}

/// [definition; agent-inferred, October 24] **A level's contact law** (the module's law).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContactLaw {
    /// `v = max(W₁ r̂ + b₁, 0)`: the contact conducts one way.
    Rectifying,
    /// `v = (W_a r̂ + b_a) ⊙ (W_b r̂ + b_b)`: the pair contact, its bilinear block learned.
    Pair,
    /// `v = (W_a r̂ + b_a) b_b + b_a (W_b r̂)`: the pair contact with its bilinear block held at
    /// zero, the foil the product is read against.
    PairLinear,
}

/// Where each family of the material sits in the one vector, and its grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LevelLayout {
    move_re: usize,
    move_im: usize,
    push_re: usize,
    push_im: usize,
    read_re: usize,
    read_im: usize,
    contact: usize,
    contact_bias: usize,
    ret: usize,
    ret_bias: usize,
    /// The gate's material and bias (empty families when ungated).
    gate: usize,
    gate_bias: usize,
    /// The turn's material and bias (empty families when unturned).
    turn: usize,
    turn_bias: usize,
    /// The pump's depth and axis, material and bias each (empty families when unpumped).
    pump: usize,
    pump_bias: usize,
    pump_axis: usize,
    pump_axis_bias: usize,
    /// The pair contact's second drive, material and bias (empty families when rectifying).
    pair: usize,
    pair_bias: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Layout {
    encoding: usize,
    levels: Vec<LevelLayout>,
    readout: usize,
    readout_bias: usize,
    len: usize,
    /// `(start, length, the family's grain)`, in order.
    families: Vec<(usize, usize, u32)>,
}

impl Layout {
    fn new(d: &TowerDeclaration) -> Self {
        let (a, w, n, f) = (d.alphabet, d.width, d.modes, d.contacts);
        let mut at = 0usize;
        let mut families = Vec::new();
        let mut take = |len: usize, grain: u32| {
            let start = at;
            at += len;
            families.push((start, len, grain));
            start
        };
        let encoding = take(a * w, FACE_BITS);
        let mut levels = Vec::with_capacity(d.levels);
        for _ in 0..d.levels {
            let mut level = LevelLayout {
                move_re: take(n, MOVE_BITS),
                move_im: take(n, MOVE_BITS),
                push_re: take(n * w, MATERIAL_BITS),
                push_im: take(n * w, MATERIAL_BITS),
                read_re: take(w * n, MATERIAL_BITS),
                read_im: take(w * n, MATERIAL_BITS),
                contact: take(f * w, MATERIAL_BITS),
                contact_bias: take(f, FACE_BITS),
                ret: take(w * f, MATERIAL_BITS),
                ret_bias: take(w, FACE_BITS),
                gate: 0,
                gate_bias: 0,
                turn: 0,
                turn_bias: 0,
                pump: 0,
                pump_bias: 0,
                pump_axis: 0,
                pump_axis_bias: 0,
                pair: 0,
                pair_bias: 0,
            };
            if d.gated {
                level.gate = take(n * w, MATERIAL_BITS);
                level.gate_bias = take(n, FACE_BITS);
            }
            if d.turned {
                level.turn = take(n * w, MATERIAL_BITS);
                level.turn_bias = take(n, FACE_BITS);
            }
            if d.pumped {
                level.pump = take(n * w, MATERIAL_BITS);
                level.pump_bias = take(n, FACE_BITS);
                level.pump_axis = take(n * w, MATERIAL_BITS);
                level.pump_axis_bias = take(n, FACE_BITS);
            }
            if d.contact != ContactLaw::Rectifying {
                level.pair = take(f * w, MATERIAL_BITS);
                level.pair_bias = take(f, FACE_BITS);
            }
            levels.push(level);
        }
        let readout = take(a * w, MATERIAL_BITS);
        let readout_bias = take(a, FACE_BITS);
        Self { encoding, levels, readout, readout_bias, len: at, families }
    }
}

/// [definition; agent-inferred] **The located material**: every family as one vector of integer
/// numerators on its grain (`Layout`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower {
    pub declaration: TowerDeclaration,
    pub theta: Vec<i32>,
    layout: Layout,
    exponential: Exponential,
    /// The exponential's face on the moves' grain, `2^(−30)`: a gated mode's `|λ|^(c r)`.
    fine: Exponential,
}

/// [definition; agent-inferred] **A stream's continuing state**: each level's modes on
/// `2^(−24)`, `(re, im)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerState {
    pub modes: Vec<Vec<(i64, i64)>>,
    /// Each level's passage credit, carried by a learner's streams (absent in a reading).
    pub credit: Option<Vec<LevelCredit>>,
}

/// [definition; agent-inferred, October 23] **A level's passage credit**: the derivative of its
/// modes' state by its own recurrence families, carried forward cell by cell as phase-carried
/// moments (the source moment, differentiated), so that a section's covector reaches the history
/// its opening state carries without a tape. Each entry is `(re, im)` on `2^(−24)` per unit of its
/// parameter. Mode `k`, input row `j`:
///
/// ```text
/// push        P_kj(t) = λ_t P_kj(t−1) + γ_t x_t[j]                  ∂h_k/∂B_re[k][j]  (∂h_k/∂B_im = i P_kj)
/// ungated     A_k(t)  = λ A_k(t−1) + h_k(t−1)                        ∂h_k/∂λ_k, its holomorphic part
///             K_k(t)  = λ K_k(t−1) + p_k(t)                          ∂h_k/∂γ_k   (p = B x before γ)
/// gated       A_k(t)  = λ_t A_k(t−1) + v_k(t) c r_t ρ_t/|λ_k|        ∂h_k/∂|λ_k|
///             K_k(t)  = λ_t K_k(t−1) + i λ_t h_k(t−1)                ∂h_k/∂φ_k
///             Q_k(t)  = λ_t Q_k(t−1) + v_k(t) ∂ρ_t/∂q                ∂h_k/∂b_g[k]
///             W_kj(t) = λ_t W_kj(t−1) + v_k(t) (∂ρ_t/∂q) x_t[j]       ∂h_k/∂W_g[k][j]
///             v_k(t)  = u_k h_k(t−1) − (ρ_t/γ_t) p_k(t)              ∂h_k(t)/∂ρ_t (zero while ρ_t is held)
/// ```
///
/// A section's opening covector `a = conj(λ_0) G_h(0)` meets them in the same shapes as the
/// section's own terms: `G_λ += conj(A) a`, `G_γ += Re(conj(a) K)`, `G_B_re += Re(conj(a) P)`, `G_B_im
/// += Re(conj(a) i P)`, and so on. The credit reaches only a level's own recurrence: the input
/// `x` a level reads from the levels below, and the encoding, are held as given, so their credit
/// stays inside the section (declared).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelCredit {
    /// `P_kj`, mode-major.
    push: Vec<(i64, i64)>,
    /// `A_k`.
    along: Vec<(i64, i64)>,
    /// `K_k`.
    around: Vec<(i64, i64)>,
    /// `Q_k` (empty when ungated).
    gate_bias: Vec<(i64, i64)>,
    /// `W_kj`, mode-major (empty when ungated).
    gate: Vec<(i64, i64)>,
}

/// One cell's face: each class's mass `2^(z_a − z_max)` on `2^(−62)`, and their sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerFace {
    pub masses: Vec<u128>,
    pub total: u128,
}

impl TowerFace {
    /// The class's code, `−log₂ p̂(a)`, on `2^(−20)` bits.
    pub fn code(&self, class: usize) -> i64 {
        let p = (self.masses[class] << UNIT_BITS) / self.total;
        -(log2_face(p.max(1), READ_BITS) as i64)
    }

    /// The face read at one base-four cell of a class (the exterior cell chart: a class index in
    /// [`cell_phases`] cells, high first; a byte takes four): the masses of the classes whose first
    /// `phase` cells are `prefix`, split by the cell at `phase`. Exact sums of the class masses;
    /// their total is the prefix's mass. A cell that holds no class of the alphabet has none.
    pub fn cell_masses(&self, prefix: usize, phase: usize) -> Result<[u128; 4]> {
        let phases = cell_phases(self.masses.len());
        if phase >= phases || prefix >> (2 * phase) != 0 {
            return refuse("a cell face needs a phase inside the class chart and a prefix inside its phase");
        }
        let low = 2 * (phases - 1 - phase);
        let mut cells = [0u128; 4];
        for d in 0..4 {
            let first = ((prefix << 2) | d) << low;
            let end = (first + (1usize << low)).min(self.masses.len());
            cells[d] = self.masses.get(first..end).map_or(0, |m| m.iter().sum());
        }
        Ok(cells)
    }
}

/// The base-four cells a class index of an alphabet of `alphabet` classes takes: the least `P`
/// with `4^P ≥ alphabet` (a byte takes four; the 1,318 founded units of `hnn::units` take six).
pub fn cell_phases(alphabet: usize) -> usize {
    let mut phases = 0;
    while (1usize << (2 * phases)) < alphabet {
        phases += 1;
    }
    phases
}

/// [definition; agent-inferred with the mathematics thread, October 24] **One cell of the tension
/// reading** ([`Tower::read_tension`]): the face the readout reads (`top`), the covector its
/// comparison with the arriving class returns (`covector`, `p̂ − q` on `2^(−24)`), and two faces the
/// readout does not read. `quadrature` is the top level's `Im(C h)`, the part of its modes the read
/// `Re(C h)` drops, on the read's own ratio grain (divided by the read's `‖r‖_rms`, so it stands on
/// `2^(−16)` beside `r̂`); `below` is the face the top level read from the level beneath it.
///
/// A receiver sums, over any partition of the passage, `H = Σ f̄ f̄ᵀ` with `f̄ = (top, 1)`,
/// `B = Σ dz f̄ᵀ` (the readout's covector the reverse scan forms) and `T = Σ dz dzᵀ`. What a
/// readout of `top` can still bridge is `B H⁺ Bᵀ`; the tension it cannot bridge is the Schur
/// complement `S = T − B H⁺ Bᵀ ⪰ 0` (atlas `contact.effective-tension`: the interior elimination
/// of `tube.dn-elimination`, with the face as the interior). A candidate face `c` bridges
/// `M Q⁺ Mᵀ` of it, `M = Σ dz cᵀ − B H⁺ Σ f̄ cᵀ`, `Q = Σ c cᵀ − (Σ f̄ cᵀ)ᵀ H⁺ Σ f̄ cᵀ`: the part of
/// the tension its own unread part carries (`contact.tension-founds-face`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensionCell {
    pub top: Vec<i32>,
    pub covector: Vec<i64>,
    pub quadrature: Vec<i32>,
    pub below: Vec<i32>,
}

/// The covector a face returns when it is compared with `target`: `dz_c = p̂(c) − [c = target]` on
/// `2^(−24)`, the cross-entropy logit gradient `p − q` at the face's grain representative. The
/// reverse scan and the tension reading ([`Tower::read_tension`]) read this one law.
fn covector(face: &TowerFace, target: usize) -> Vec<i64> {
    (0..face.masses.len())
        .map(|c| {
            let p = ((face.masses[c] << COVECTOR_BITS) + face.total / 2) / face.total;
            p as i64 - if c == target { 1i64 << COVECTOR_BITS } else { 0 }
        })
        .collect()
}

/// `max |w|` over a family.
fn reach(w: &[i32]) -> u64 {
    w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0)
}

/// `out[o] = release(Σ_i w[o·cols + i] x[i] + bias[o] · 2^bias_shift, shift)`, in `i64` where the
/// terms' bound allows and in `i128` otherwise; `x` a face carried in `i32` or `i64`.
fn affine<V: Copy + Into<i64>>(w: &[i32], wmax: u64, cols: usize, x: &[V], bias: Option<&[i32]>, bias_shift: u32, shift: u32, out: &mut [i64]) -> Result<()> {
    let xmax = x.iter().map(|&v| v.into().unsigned_abs()).max().unwrap_or(0);
    let terms = (wmax as u128) * (xmax as u128) * (cols as u128 + 1);
    if terms >= 1u128 << 126 {
        return refuse("an affine sum outgrew its 128-bit carrier");
    }
    let narrow = terms < (1u128 << 62);
    for (o, slot) in out.iter_mut().enumerate() {
        let row = &w[o * cols..(o + 1) * cols];
        let mut sum: i128 = if narrow {
            row.iter().zip(x).map(|(a, &b)| *a as i64 * b.into()).sum::<i64>() as i128
        } else {
            row.iter().zip(x).map(|(a, &b)| *a as i128 * b.into() as i128).sum::<i128>()
        };
        if let Some(b) = bias {
            sum += (b[o] as i128) << bias_shift;
        }
        *slot = fit64(release(sum, shift))?;
    }
    Ok(())
}

/// `out[i] = release(Σ_o w[o·cols + i] y[o], shift)`: the transposed read, `y` a covector (carried
/// in `i64`: the reverse scan accumulates a slow mode's covector over the section).
fn transposed(w: &[i32], wmax: u64, cols: usize, y: &[i64], shift: u32, out: &mut [i64]) -> Result<()> {
    let ymax = reach64(y);
    let rows = y.len();
    let narrow = (wmax as u128) * (ymax as u128) * (rows as u128 + 1) < (1u128 << 62);
    if narrow {
        let mut acc = vec![0i64; cols];
        for (o, &yo) in y.iter().enumerate() {
            if yo == 0 {
                continue;
            }
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i64 * yo;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a as i128, shift))?;
        }
    } else {
        let mut acc = vec![0i128; cols];
        for (o, &yo) in y.iter().enumerate() {
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i128 * yo as i128;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a, shift))?;
        }
    }
    Ok(())
}

/// `g[o·cols + i] += Σ_t y_t[o] x_t[i]`: a section's outer products of covectors with faces, at
/// their summed grain. Integer addition is associative, so summing over the section's cells before
/// the sum reaches the gradient gives the bits one product a cell gives; the sum runs in `i64` where
/// the terms' bound `Σ_t max|y_t| max|x_t|` allows it, in `i128` below `2^126`, and is refused past
/// it. A face `x` is carried in `i32` or `i64`.
fn outer_sum<Y: AsRef<[i64]>, X: AsRef<[V]>, V: Copy + Into<i64>>(g: &mut [i128], cols: usize, ys: &[Y], xs: &[X]) -> Result<()> {
    let mut bound = 0u128;
    for (y, x) in ys.iter().zip(xs) {
        let xmax = x.as_ref().iter().map(|&v| v.into().unsigned_abs()).max().unwrap_or(0);
        bound = bound.checked_add(reach64(y.as_ref()) as u128 * xmax as u128).filter(|&b| b < 1u128 << 126).ok_or(TowerError::Refused("an outer sum outgrew its 128-bit carrier"))?;
    }
    for (o, row) in g.chunks_exact_mut(cols).enumerate() {
        if bound < (1u128 << 62) {
            let mut acc = vec![0i64; cols];
            for (y, x) in ys.iter().zip(xs) {
                let yo = y.as_ref()[o];
                if yo != 0 {
                    for (a, &xv) in acc.iter_mut().zip(x.as_ref()) {
                        *a += yo * xv.into();
                    }
                }
            }
            for (slot, a) in row.iter_mut().zip(acc) {
                *slot += a as i128;
            }
        } else {
            for (y, x) in ys.iter().zip(xs) {
                let yo = y.as_ref()[o] as i128;
                if yo != 0 {
                    for (slot, &xv) in row.iter_mut().zip(x.as_ref()) {
                        *slot += yo * xv.into() as i128;
                    }
                }
            }
        }
    }
    Ok(())
}

/// `max |y|` over a covector.
fn reach64(y: &[i64]) -> u64 {
    y.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0)
}

/// A fallible map of known length collected into one allocation: `collect::<Result<Vec<_>>>`
/// cannot read the length through its adapter and grows the vector by reallocation, which crosses
/// the allocator's lock between the parallel streams.
fn collect_exact<T>(items: impl ExactSizeIterator<Item = Result<T>>) -> Result<Vec<T>> {
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        out.push(item?);
    }
    Ok(out)
}

fn to32(v: &[i64], what: &'static str) -> Result<Vec<i32>> {
    collect_exact(v.iter().map(|&x| fit32(x as i128, what)))
}

/// One level's forward temporaries at one cell.
#[derive(Clone, Debug, Default)]
struct LevelCell {
    input: Vec<i32>,
    /// `B x` before the mode's `γ`, on the state's grain.
    push: Vec<(i64, i64)>,
    state: Vec<(i64, i64)>,
    state_face: Vec<i64>,
    /// `r̂`, the contacts' input, on `2^(−16)`.
    read: Vec<i32>,
    /// `‖r‖_rms` on `2^(−16)` (zero when the face is zero).
    read_scale: i128,
    drive: Vec<i32>,
    /// The pair contact's second drive `W_b r̂ + b_b` (empty when rectifying).
    pair: Vec<i32>,
    conduct: Vec<i32>,
    /// The gated modes' moves at this cell (empty when ungated).
    gate: Vec<GatedMove>,
}

/// A gated mode's move at one cell: the gate `r` and `λ_t`, `ρ_t = |λ_t|`, `γ_t` on `2^(−30)`, and
/// whether `ρ_t` was held at the margin. A pumped mode's `lam` is its turn `α_t`, beside the pump
/// `β_t = ρ_t κ_t P_t`.
#[derive(Clone, Copy, Debug, Default)]
struct GatedMove {
    open: i64,
    /// `λ_t/ρ_t`: the founded unit, turned by the arriving symbol when the mode is turned.
    unit: (i64, i64),
    lam: (i64, i64),
    rho: i64,
    gamma: i64,
    held: bool,
    /// The pump's opening `r`, depth `κ = 2r − 1`, axis face `P` and `β`, on `2^(−30)` (zero when
    /// unpumped).
    pump_open: i64,
    kappa: i64,
    axis: (i64, i64),
    beta: (i64, i64),
}

/// A gated level's founded moves read once a section: `u = λ/|λ|`, `|λ|` and `ℓ = log₂|λ|` on
/// `2^(−30)`.
#[derive(Clone, Debug, Default)]
struct GateFaces {
    units: Vec<(i128, i128)>,
    moduli: Vec<i128>,
    logs: Vec<i128>,
}

/// The gate's reach `c`: the founded modulus raised by `c r`, so the gate's midpoint `r = ½`
/// reproduces it and the log-decay is scaled inside `(0, 2)` (agent-inferred).
const GATE_REACH: i128 = 2;

/// The moves' margin radius `1 − 2^(−12)` on `2^(−30)`.
fn radius() -> i128 {
    (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - MARGIN))
}

/// `r = 1/(1 + 2^(−q))` on `2^(−30)`, `q` on `2^(−16)`: the base-two logistic, through the face's
/// exponential navigator.
fn logistic(exponential: &Exponential, q: i64) -> i128 {
    let unit = 1i128 << UNIT_BITS;
    if q >= 0 {
        let e = exponential.below_one(-(q as i128)) as i128;
        div_nearest(1i128 << (UNIT_BITS + MOVE_BITS), unit + e)
    } else {
        let e = exponential.below_one(q as i128) as i128;
        div_nearest(e << MOVE_BITS, unit + e)
    }
}

/// One cell's forward temporaries.
#[derive(Clone, Debug, Default)]
struct Cell {
    levels: Vec<LevelCell>,
    top: Vec<i32>,
    face: TowerFace,
}

impl Default for TowerFace {
    fn default() -> Self {
        Self { masses: Vec::new(), total: 1 }
    }
}

/// The reaches of every family, read once a section.
#[derive(Clone, Debug)]
struct Reaches {
    /// Per level: push (re, im), read (re, im), contact, return, gate, turn, pump, pump axis, the
    /// pair contact's second drive.
    levels: Vec<[u64; 11]>,
    /// The turned modes' ladder `e^(iπ/2^i)`, `i = 0..=TURN_BITS`, on `2^(−30)`, and the half turn
    /// `π` on `2^(−30)` (empty and zero when unturned).
    ladder: Vec<(i128, i128)>,
    half_turn: i128,
    readout: u64,
    /// Each level's `γ_k = √(1 − |λ_k|²)` on `2^(−30)`.
    gammas: Vec<Vec<i128>>,
    /// Each gated level's founded moves (empty when ungated).
    gates: Vec<GateFaces>,
}

/// `x / k` to the nearest integer, half away from zero.
fn div_nearest(x: i128, k: i128) -> i128 {
    if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }
}

/// `e^(a + i b)` on `2^(−30)`, `a`, `b` on `2^(−30)`: the series summed until its term releases
/// to zero at the grain.
fn exp_series(a: i128, b: i128) -> (i128, i128) {
    let mut term = (1i128 << MOVE_BITS, 0i128);
    let mut sum = term;
    let mut k = 1i128;
    loop {
        let re = release(term.0 * a - term.1 * b, MOVE_BITS);
        let im = release(term.0 * b + term.1 * a, MOVE_BITS);
        term = (div_nearest(re, k), div_nearest(im, k));
        if term == (0, 0) {
            return sum;
        }
        sum = (sum.0 + term.0, sum.1 + term.1);
        k += 1;
    }
}

/// The turned mode's grain: a turn is read in half turns on `2^(−16)`, the face's grain.
const TURN_BITS: u32 = FACE_BITS;

/// The turn's spread over a level's width, `⌈log₂ w⌉`: the arriving drive is read as its mean over
/// the width, `s_t = 2^(−spread) (W_φ x + b_φ)`, so a deposit that moves every one of a mode's turn
/// weights by one rate step turns the mode by that step's share of a half turn, as a gate's moves
/// its logit by a share of a doubling. [agent-inferred, October 23: read at the full drive, one
/// rate step `2^(−7)` over 64 inputs of unit size turned a mode by up to half a half turn, and the
/// terrain's second pass coded more bits section after section as the certificate halved its
/// steps 626 times.]
fn turn_spread(width: usize) -> u32 {
    usize::BITS - width.saturating_sub(1).leading_zeros()
}

/// `e^(iπ/2^i)` on `2^(−30)` for `i = 0..=TURN_BITS`: the half turn, the quarter turn, then each
/// half angle, `cos(θ/2) = √((1 + cos θ)/2)` and `sin(θ/2) = sin θ/(2 cos(θ/2))` (the sine by the
/// quotient, which keeps its relative grain where `1 − cos θ` would not), on `2^(−60)` released
/// once.
fn turn_ladder_faces() -> Vec<(i128, i128)> {
    const FINE: u32 = 60;
    let one = 1i128 << FINE;
    let mut out = vec![(-(1i128 << MOVE_BITS), 0), (0, 1i128 << MOVE_BITS)];
    let (mut c, mut s) = (0i128, one);
    for _ in 1..TURN_BITS {
        let half = ((((one + c) as u128) << FINE) >> 1).isqrt() as i128;
        s = div_nearest(s << FINE, 2 * half);
        c = half;
        out.push((release(c, FINE - MOVE_BITS), release(s, FINE - MOVE_BITS)));
    }
    out
}

/// `π` on `2^(−bits)` by Machin's series `π = 16 atan(1/5) − 4 atan(1/239)`, each term an exact
/// quotient sixteen grains finer, released once: the half turn's navigator face.
fn half_turn(bits: u32) -> i128 {
    const GUARD: u32 = 16;
    let one = 1i128 << (bits + GUARD);
    let atan_inverse = |k: i128| -> i128 {
        let (mut power, mut sum, mut n) = (one / k, 0i128, 0i128);
        while power != 0 {
            let term = power / (2 * n + 1);
            sum += if n % 2 == 0 { term } else { -term };
            power /= k * k;
            n += 1;
        }
        sum
    };
    release(16 * atan_inverse(5) - 4 * atan_inverse(239), GUARD)
}

/// `e^(iπ s)` on `2^(−30)` for a turn `s` in half turns on `2^(−16)`: `s` read modulo the full
/// turn and composed from the ladder's dyadic turns, its binary digits from the half turn down.
fn turn_face(s: i64, ladder: &[(i128, i128)]) -> (i128, i128) {
    let full = 1i64 << (TURN_BITS + 1);
    let j = s.rem_euclid(full) as u64;
    let mut value = (1i128 << MOVE_BITS, 0i128);
    for (i, &(cr, ci)) in ladder.iter().enumerate() {
        if j & (1u64 << (TURN_BITS as usize - i)) != 0 {
            value = (release(value.0 * cr - value.1 * ci, MOVE_BITS), release(value.0 * ci + value.1 * cr, MOVE_BITS));
        }
    }
    value
}

/// `r̂ = r / ‖r‖_rms` on `2^(−16)` and `‖r‖_rms` on `2^(−16)`, `r` on `2^(−16)`; a zero face reads
/// as zero.
fn ratio_to_power(r: &[i64]) -> Result<(Vec<i32>, i128)> {
    let power: i128 = r.iter().map(|&v| v as i128 * v as i128).sum();
    let scale = ((power / r.len() as i128) as u128).isqrt() as i128;
    if scale == 0 {
        return Ok((vec![0; r.len()], 0));
    }
    let read = collect_exact(r.iter().map(|&v| fit32(div_nearest((v as i128) << FACE_BITS, scale), "a read's ratio outgrew its 32-bit carrier")))?;
    Ok((read, scale))
}

/// The adjoint of [`ratio_to_power`]: `∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms`, covectors on
/// `2^(−24)`.
fn ratio_adjoint(read: &[i32], scale: i128, cov: &[i64]) -> Result<Vec<i64>> {
    if scale == 0 {
        return Ok(vec![0; cov.len()]);
    }
    let dot: i128 = read.iter().zip(cov).map(|(&a, &b)| a as i128 * b as i128).sum(); // 2^(−40)
    let mean = div_nearest(dot, read.len() as i128);
    collect_exact(read.iter().zip(cov).map(|(&a, &b)| fit64(div_nearest((b as i128 - release(mean * a as i128, 2 * FACE_BITS)) << FACE_BITS, scale))))
}

/// `|λ|` on `2^(−30)` and `γ = √(1 − |λ|²)` on `2^(−30)`.
fn modulus_and_gamma(re: i128, im: i128) -> (i128, i128) {
    let n = re * re + im * im;
    let modulus = (n as u128).isqrt() as i128;
    let gamma = (((1i128 << (2 * MOVE_BITS)) - n).max(0) as u128).isqrt() as i128;
    (modulus, gamma)
}

impl Tower {
    /// **The founding configuration** (agent-inferred, October 23), read from a declared exterior
    /// key stream (`keys`, consumed four bytes a key, each a signed 32-bit integer read as a
    /// uniform draw on `[−1, 1)`): the encoding uniform on `[−1, 1)`; each level's modes on a
    /// scale ladder `ρ = 1 − 2^(−s)` for `s = 1..=S` and a turn ladder `j·π/J`, `J = N/S` (the
    /// odometer's mixed radix and a closing ring's characters), the push by `1/√d` (the step
    /// scales it by the mode's `γ`, so a mode's state opens at the face's scale), the read by `1/√N`, the contacts
    /// by `√(6/d)` (a rectifier passes half its drive); the return and the readout at zero, so the
    /// tower opens on the flat face (birth at zero) and each level on the identity.
    pub fn found(declaration: TowerDeclaration, keys: &[u8]) -> Result<Self> {
        let d = declaration;
        if d.alphabet < 2 || d.width == 0 || d.modes == 0 || d.contacts == 0 || d.levels == 0 {
            return refuse("a tower needs two classes and a nonempty width, bank, contacts and levels");
        }
        if d.turned && !d.gated {
            return refuse("a turned mode is a gated mode");
        }
        if d.pumped && !d.turned {
            return refuse("a pumped mode is a turned mode");
        }
        let layout = Layout::new(&d);
        let mut theta = vec![0i32; layout.len];
        let mut cursor = 0usize;
        let mut draw = || -> Result<i64> {
            let word = keys.get(cursor..cursor + 4).ok_or(TowerError::Refused("fewer key bytes than the founding reads"))?;
            cursor += 4;
            Ok(i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i64)
        };
        // A uniform draw on [−r, r) with r = num/den on the grain 2^(−bits).
        let mut uniform = |slice: &mut [i32], num: u128, den: u128, bits: u32| -> Result<()> {
            for v in slice.iter_mut() {
                let k = draw()? as i128; // on 2^(−31), in [−1, 1)
                let scaled = (k * ((num << bits) / den) as i128) >> 31;
                *v = fit32(scaled, "a founded value outgrew its 32-bit carrier")?;
            }
            Ok(())
        };
        let e = layout.encoding;
        uniform(&mut theta[e..e + d.alphabet * d.width], 1, 1, FACE_BITS)?;
        let turns = turn_ladder(d.modes);
        let sqrt_width = (d.width as u128).isqrt().max(1);
        for lv in &layout.levels {
            for k in 0..d.modes {
                let s = (k / turns) as u32 + 1;
                let j = (k % turns) as u64;
                let rho = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - s.min(MARGIN)));
                // The turn by j·π/turns: turns is a power of two by the ladder's declaration.
                let n = turns.trailing_zeros();
                let rot = dyadic_turn(j, n, MOVE_BITS);
                let re = release(rot.re * rho, MOVE_BITS);
                let im = release(rot.im * rho, MOVE_BITS);
                theta[lv.move_re + k] = fit32(re, "a founded move outgrew its 32-bit carrier")?;
                theta[lv.move_im + k] = fit32(im, "a founded move outgrew its 32-bit carrier")?;
                // The push at 1/√d; the step scales it by the mode's γ = √(1 − |λ|²).
                let row = lv.push_re + k * d.width;
                uniform(&mut theta[row..row + d.width], 1, sqrt_width, MATERIAL_BITS)?;
                let row = lv.push_im + k * d.width;
                uniform(&mut theta[row..row + d.width], 1, sqrt_width, MATERIAL_BITS)?;
            }
            let sqrt_modes = (d.modes as u128).isqrt().max(1);
            uniform(&mut theta[lv.read_re..lv.read_re + d.width * d.modes], 1, sqrt_modes, MATERIAL_BITS)?;
            uniform(&mut theta[lv.read_im..lv.read_im + d.width * d.modes], 1, sqrt_modes, MATERIAL_BITS)?;
            // √(6/d) as (√6·2^16)/(√d·2^16), each square root on 2^(−16).
            let six = (6u128 << 32).isqrt();
            let dd = ((d.width as u128) << 32).isqrt();
            uniform(&mut theta[lv.contact..lv.contact + d.contacts * d.width], six, dd, MATERIAL_BITS)?;
            // The pair contact's second drive at zero material and unit bias: it opens one-sided.
            if d.contact != ContactLaw::Rectifying {
                theta[lv.pair_bias..lv.pair_bias + d.contacts].fill(1 << FACE_BITS);
            }
        }
        // The gate's material and bias open at zero: r = ½, the founded move; the turn's at zero,
        // so a turned tower opens on its gated twin; the pump's at zero (κ = 0, β = 0), so a pumped
        // tower opens on its turned twin.
        Ok(Self { declaration: d, theta, layout, exponential: Exponential::new(FACE_BITS), fine: Exponential::new(MOVE_BITS) })
    }

    /// The rested state: every mode at zero.
    pub fn rest(&self) -> TowerState {
        TowerState { modes: vec![vec![(0, 0); self.declaration.modes]; self.declaration.levels], credit: None }
    }

    /// A learner's rested stream: every mode and every credit moment at zero.
    pub fn rest_with_credit(&self) -> TowerState {
        let d = &self.declaration;
        let (n, w) = (d.modes, d.width);
        let gated = if d.gated { 1 } else { 0 };
        let level = LevelCredit {
            push: vec![(0, 0); n * w],
            along: vec![(0, 0); n],
            around: vec![(0, 0); n],
            gate_bias: vec![(0, 0); gated * n],
            gate: vec![(0, 0); gated * n * w],
        };
        TowerState { credit: Some(vec![level; d.levels]), ..self.rest() }
    }

    fn reaches(&self) -> Reaches {
        let t = &self.theta;
        let d = &self.declaration;
        let levels = self
            .layout
            .levels
            .iter()
            .map(|lv| {
                [
                    reach(&t[lv.push_re..lv.push_re + d.modes * d.width]),
                    reach(&t[lv.push_im..lv.push_im + d.modes * d.width]),
                    reach(&t[lv.read_re..lv.read_re + d.width * d.modes]),
                    reach(&t[lv.read_im..lv.read_im + d.width * d.modes]),
                    reach(&t[lv.contact..lv.contact + d.contacts * d.width]),
                    reach(&t[lv.ret..lv.ret + d.width * d.contacts]),
                    if d.gated { reach(&t[lv.gate..lv.gate + d.modes * d.width]) } else { 0 },
                    if d.turned { reach(&t[lv.turn..lv.turn + d.modes * d.width]) } else { 0 },
                    if d.pumped { reach(&t[lv.pump..lv.pump + d.modes * d.width]) } else { 0 },
                    if d.pumped { reach(&t[lv.pump_axis..lv.pump_axis + d.modes * d.width]) } else { 0 },
                    if d.contact != ContactLaw::Rectifying { reach(&t[lv.pair..lv.pair + d.contacts * d.width]) } else { 0 },
                ]
            })
            .collect();
        let gammas = self
            .layout
            .levels
            .iter()
            .map(|lv| (0..d.modes).map(|k| modulus_and_gamma(t[lv.move_re + k] as i128, t[lv.move_im + k] as i128).1).collect())
            .collect();
        let one = 1i128 << MOVE_BITS;
        let gates = if !d.gated {
            Vec::new()
        } else {
            self.layout
                .levels
                .iter()
                .map(|lv| {
                    let mut faces = GateFaces::default();
                    for k in 0..d.modes {
                        let (re, im) = (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128);
                        let (modulus, _) = modulus_and_gamma(re, im);
                        // u = λ/|λ| over the modulus rounded up and quotients toward zero, so
                        // |u| ≤ 1 exactly: a closed gate (r → 0) moves at ρ → 1 whatever |λ|, and a
                        // unit rounded past the circle would then carry |λ_t| past one and γ_t to zero.
                        let above = modulus + i128::from(modulus * modulus < re * re + im * im);
                        let unit = if modulus == 0 { (one, 0) } else { (re * one / above, im * one / above) };
                        faces.units.push(unit);
                        faces.moduli.push(modulus);
                        // log₂|λ| on 2^(−30), |λ| re-based to 2^(−62); a zero move reads at one grain.
                        faces.logs.push(log2_face((modulus.max(1) as u128) << (UNIT_BITS - MOVE_BITS), MOVE_BITS));
                    }
                    faces
                })
                .collect()
        };
        let (ladder, half_turn) = if d.turned { (turn_ladder_faces(), half_turn(MOVE_BITS)) } else { (Vec::new(), 0) };
        Reaches { levels, readout: reach(&t[self.layout.readout..self.layout.readout + d.alphabet * d.width]), gammas, gates, ladder, half_turn }
    }

    /// One cell forward: the class `u` arrives, every level's modes move, and the face of the next
    /// class is read. The temporaries are returned for the reverse scan.
    fn step(&self, state: &mut TowerState, u: usize, reaches: &Reaches) -> Result<Cell> {
        let d = &self.declaration;
        let (w, n, f) = (d.width, d.modes, d.contacts);
        if u >= d.alphabet {
            return refuse("a class outside the declared alphabet");
        }
        let t = &self.theta;
        let e = self.layout.encoding + u * w;
        let mut x: Vec<i32> = t[e..e + w].to_vec();
        let mut levels = Vec::with_capacity(d.levels);
        let mut buf = vec![0i64; w.max(n).max(f)];
        for (l, lv) in self.layout.levels.iter().enumerate() {
            let r = &reaches.levels[l];
            // The push, on 2^(−40) released to the state's 2^(−24).
            let mut push_re = vec![0i64; n];
            let mut push_im = vec![0i64; n];
            affine(&t[lv.push_re..lv.push_re + n * w], r[0], w, &x, None, 0, MATERIAL_BITS + FACE_BITS - STATE_BITS, &mut push_re)?;
            affine(&t[lv.push_im..lv.push_im + n * w], r[1], w, &x, None, 0, MATERIAL_BITS + FACE_BITS - STATE_BITS, &mut push_im)?;
            // The gated move at this cell: λ_t = |λ|^(c r) u, held at the margin, γ_t = √(1 − |λ_t|²).
            let mut gate = Vec::new();
            if d.gated {
                let faces = &reaches.gates[l];
                let mut q = vec![0i64; n];
                affine(&t[lv.gate..lv.gate + n * w], r[6], w, &x, Some(&t[lv.gate_bias..lv.gate_bias + n]), MATERIAL_BITS, MATERIAL_BITS, &mut q)?;
                // The arriving symbol's turn `s_t = 2^(−spread) (W_φ x + b_φ)`, in half turns on 2^(−16).
                let mut turns = vec![0i64; if d.turned { n } else { 0 }];
                if d.turned {
                    affine(&t[lv.turn..lv.turn + n * w], r[7], w, &x, Some(&t[lv.turn_bias..lv.turn_bias + n]), MATERIAL_BITS, MATERIAL_BITS, &mut turns)?;
                    for v in &mut turns {
                        *v = fit64(release(*v as i128, turn_spread(w)))?;
                    }
                }
                // The pump's depth logit `W_κ x + b_κ` on 2^(−16), and its axis
                // `p_t = 2^(−spread) (W_ψ x + b_ψ)` in half turns on 2^(−16).
                let mut depths = vec![0i64; if d.pumped { n } else { 0 }];
                let mut axes = vec![0i64; if d.pumped { n } else { 0 }];
                if d.pumped {
                    affine(&t[lv.pump..lv.pump + n * w], r[8], w, &x, Some(&t[lv.pump_bias..lv.pump_bias + n]), MATERIAL_BITS, MATERIAL_BITS, &mut depths)?;
                    affine(&t[lv.pump_axis..lv.pump_axis + n * w], r[9], w, &x, Some(&t[lv.pump_axis_bias..lv.pump_axis_bias + n]), MATERIAL_BITS, MATERIAL_BITS, &mut axes)?;
                    for v in &mut axes {
                        *v = fit64(release(*v as i128, turn_spread(w)))?;
                    }
                }
                gate.reserve_exact(n);
                for k in 0..n {
                    let open = logistic(&self.exponential, q[k]);
                    let exponent = release(GATE_REACH * open * faces.logs[k], MOVE_BITS);
                    let mut rho = release(self.fine.below_one(exponent) as i128, UNIT_BITS - MOVE_BITS);
                    let held = rho > radius();
                    if held {
                        rho = radius();
                    }
                    let (mut ur, mut ui) = faces.units[k];
                    if d.turned {
                        let (tr, ti) = turn_face(turns[k], &reaches.ladder);
                        (ur, ui) = (release(ur * tr - ui * ti, MOVE_BITS), release(ur * ti + ui * tr, MOVE_BITS));
                    }
                    let (lr, li) = (release(rho * ur, MOVE_BITS), release(rho * ui, MOVE_BITS));
                    let (_, gamma) = modulus_and_gamma(lr, li);
                    if gamma == 0 {
                        return refuse("a gated move reached the unit circle");
                    }
                    let mut moved = GatedMove { open: open as i64, unit: (ur as i64, ui as i64), lam: (lr as i64, li as i64), rho: rho as i64, gamma: gamma as i64, held, ..GatedMove::default() };
                    if d.pumped {
                        // α_t = ρ_t (1 − |κ|) U_t and β_t = ρ_t κ P_t: |α| + |β| = ρ_t, so γ_t is kept.
                        let one = 1i128 << MOVE_BITS;
                        let pump_open = logistic(&self.exponential, depths[k]);
                        let kappa = 2 * pump_open - one;
                        let (ar, ai) = turn_face(axes[k], &reaches.ladder);
                        let keep = one - kappa.abs();
                        let depth = release(rho * kappa, MOVE_BITS);
                        moved.lam = (release(keep * lr, MOVE_BITS) as i64, release(keep * li, MOVE_BITS) as i64);
                        moved.beta = (release(depth * ar, MOVE_BITS) as i64, release(depth * ai, MOVE_BITS) as i64);
                        moved.pump_open = pump_open as i64;
                        moved.kappa = kappa as i64;
                        moved.axis = (ar as i64, ai as i64);
                    }
                    gate.push(moved);
                }
            }
            let modes = &mut state.modes[l];
            let gammas = &reaches.gammas[l];
            let mut face = vec![0i64; 2 * n];
            for k in 0..n {
                let (hr, hi) = modes[k];
                let ((lr, li), gamma) = match gate.get(k) {
                    Some(m) => ((m.lam.0 as i128, m.lam.1 as i128), m.gamma as i128),
                    None => ((t[lv.move_re + k] as i128, t[lv.move_im + k] as i128), gammas[k]),
                };
                // The pump's reflection β conj(h) (zero unless pumped).
                let (br, bi) = gate.get(k).map_or((0, 0), |m| (m.beta.0 as i128, m.beta.1 as i128));
                let (hr, hi) = (hr as i128, hi as i128);
                let pr = release(gamma * push_re[k] as i128, MOVE_BITS);
                let pi = release(gamma * push_im[k] as i128, MOVE_BITS);
                let nr = fit64(release(lr * hr - li * hi + br * hr + bi * hi, MOVE_BITS) + pr)?;
                let ni = fit64(release(lr * hi + li * hr + bi * hr - br * hi, MOVE_BITS) + pi)?;
                modes[k] = (nr, ni);
                face[k] = fit64(release(nr as i128, STATE_BITS - FACE_BITS))?;
                face[n + k] = fit64(release(ni as i128, STATE_BITS - FACE_BITS))?;
            }
            // The read Re(C h) = C_re h_re − C_im h_im, on 2^(−40) released to 2^(−16).
            let mut read_a = vec![0i64; w];
            let mut read_b = vec![0i64; w];
            affine(&t[lv.read_re..lv.read_re + w * n], r[2], n, &face[..n], None, 0, 0, &mut read_a)?;
            affine(&t[lv.read_im..lv.read_im + w * n], r[3], n, &face[n..], None, 0, 0, &mut read_b)?;
            // The raw read is carried in 64 bits: only its direction reaches the contacts, so its
            // scale is a gauge, and the normalized step lets it grow (see "The read's carrier").
            let raw: Vec<i64> = collect_exact(read_a.iter().zip(&read_b).map(|(a, b)| fit64(release(*a as i128 - *b as i128, MATERIAL_BITS))))?;
            let (read, read_scale) = ratio_to_power(&raw)?;
            let drive_buf = &mut buf[..f];
            affine(&t[lv.contact..lv.contact + f * w], r[4], w, &read, Some(&t[lv.contact_bias..lv.contact_bias + f]), MATERIAL_BITS, MATERIAL_BITS, drive_buf)?;
            let drive = to32(drive_buf, "a contact drive outgrew its 32-bit carrier")?;
            let (conduct, pair) = match d.contact {
                ContactLaw::Rectifying => (drive.iter().map(|&a| a.max(0)).collect(), Vec::new()),
                law => {
                    // The second drive W_b r̂ + b_b, and v = a ⊙ b on 2^(−32) released to the face
                    // (the foil: a b_b + b_a (b − b_b), the product's block held at zero).
                    let mut second = vec![0i64; f];
                    affine(&t[lv.pair..lv.pair + f * w], r[10], w, &read, Some(&t[lv.pair_bias..lv.pair_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut second)?;
                    let second = to32(&second, "a pair contact's second drive outgrew its 32-bit carrier")?;
                    let conduct = collect_exact((0..f).map(|o| {
                        let (a, b) = (drive[o] as i128, second[o] as i128);
                        let product = match law {
                            ContactLaw::Pair => a * b,
                            _ => {
                                let (ba, bb) = (t[lv.contact_bias + o] as i128, t[lv.pair_bias + o] as i128);
                                a * bb + ba * (b - bb)
                            }
                        };
                        fit32(release(product, FACE_BITS), "a pair contact's conduction outgrew its 32-bit carrier")
                    }))?;
                    (conduct, second)
                }
            };
            let mut ret = vec![0i64; w];
            affine(&t[lv.ret..lv.ret + w * f], r[5], f, &conduct, Some(&t[lv.ret_bias..lv.ret_bias + w]), MATERIAL_BITS, MATERIAL_BITS, &mut ret)?;
            let next: Vec<i32> = collect_exact(x.iter().zip(&ret).map(|(a, b)| fit32(*a as i128 + *b as i128, "the residual stream outgrew its 32-bit carrier")))?;
            let state_copy = modes.clone();
            let push = push_re.into_iter().zip(push_im).collect();
            levels.push(LevelCell { input: std::mem::replace(&mut x, next), push, state: state_copy, state_face: face, read, read_scale, drive, pair, conduct, gate });
        }
        let a = d.alphabet;
        let mut z = vec![0i64; a];
        let ro = self.layout.readout;
        let rb = self.layout.readout_bias;
        affine(&t[ro..ro + a * w], reaches.readout, w, &x, Some(&t[rb..rb + a]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
        let zmax = *z.iter().max().expect("a nonempty alphabet");
        let masses: Vec<u128> = z.iter().map(|&v| self.exponential.below_one((v - zmax) as i128)).collect();
        let total = masses.iter().sum();
        Ok(Cell { levels, top: x, face: TowerFace { masses, total } })
    }

    /// The face of the next class after `u` arrives, and the state moved.
    pub fn advance(&self, state: &mut TowerState, u: usize) -> Result<TowerFace> {
        let reaches = self.reaches();
        Ok(self.step(state, u, &reaches)?.face)
    }

    /// A section's forward: `classes[0..T]` arrive, `classes[1..=T]` are coded.
    fn forward(&self, state: &mut TowerState, classes: &[usize], reaches: &Reaches) -> Result<Vec<Cell>> {
        collect_exact(classes[..classes.len() - 1].iter().map(|&u| self.step(state, u, reaches)))
    }

    /// The reverse scan of one stream's section: the covector of every family, on its natural
    /// grain (material `2^(−40)`, faces and biases `2^(−24)`, moves `2^(−48)`).
    fn reverse(&self, opening: &TowerState, cells: &[Cell], classes: &[usize], compared: Option<&[Option<usize>]>) -> Result<Vec<i128>> {
        self.reverse_joined(opening, cells, classes, None, compared)
    }

    /// The reverse scan with a covector reaching each cell's top from outside the tower (the
    /// duplex's meeting, `duplex`), on the top covector's grain `2^(−24)`, added to the one the
    /// tower's own face sends there. `compared` declares, place by place, the class each face is
    /// compared with (the class that arrived when it is `None`): a place with no comparison is the
    /// tower's own release re-entering what it reads, which brings no news, so its face sends no
    /// covector, while the covectors of the places after it still return through the state it
    /// moved; a place compared with another class than the one read there is the tower's own
    /// release read against the truth where the two part.
    fn reverse_joined(
        &self,
        opening: &TowerState,
        cells: &[Cell],
        classes: &[usize],
        joined: Option<&[Vec<i64>]>,
        compared: Option<&[Option<usize>]>,
    ) -> Result<Vec<i128>> {
        let d = &self.declaration;
        let (w, n, f, a) = (d.width, d.modes, d.contacts, d.alphabet);
        let t = &self.theta;
        let reaches = self.reaches();
        let ln2 = ln2_face();
        let ln2_square = release(ln2 * ln2, MOVE_BITS);
        let mut g = vec![0i128; self.layout.len];
        let cells_n = cells.len();
        // The face's covector and the top's.
        let mut dx: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
        let mut dzs: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
        let ro = self.layout.readout;
        let rb = self.layout.readout_bias;
        if compared.is_some_and(|m| m.len() != classes.len()) {
            return refuse("a comparison for each class of the section");
        }
        for (i, cell) in cells.iter().enumerate() {
            let target = compared.map_or(Some(classes[i + 1]), |m| m[i + 1]);
            let face = &cell.face;
            let dz: Vec<i64> = match target {
                Some(target) => covector(face, target),
                None => vec![0; a],
            };
            for (slot, &v) in g[rb..rb + a].iter_mut().zip(&dz) {
                *slot += v as i128;
            }
            let mut back = vec![0i64; w];
            transposed(&t[ro..ro + a * w], reaches.readout, w, &dz, MATERIAL_BITS, &mut back)?;
            dx.push(back);
            dzs.push(dz);
        }
        let tops: Vec<&[i32]> = cells.iter().map(|cell| cell.top.as_slice()).collect();
        outer_sum(&mut g[ro..ro + a * w], w, &dzs, &tops)?;
        if let Some(joined) = joined {
            if joined.len() != cells_n {
                return refuse("a joined covector for each cell of the section");
            }
            for (top, extra) in dx.iter_mut().zip(joined) {
                for (v, e) in top.iter_mut().zip(extra) {
                    *v = fit64(*v as i128 + *e as i128)?;
                }
            }
        }
        for l in (0..d.levels).rev() {
            let lv = self.layout.levels[l];
            let r = &reaches.levels[l];
            let mut read_cov: Vec<Vec<(i64, i64)>> = Vec::with_capacity(cells_n);
            let mut das: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
            let mut dbs: Vec<Vec<i64>> = Vec::with_capacity(if d.contact != ContactLaw::Rectifying { cells_n } else { 0 });
            let mut dreads: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
            let mut negs: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
            for (i, cell) in cells.iter().enumerate() {
                let lc = &cell.levels[l];
                let dy = &dx[i];
                for (slot, &v) in g[lv.ret_bias..lv.ret_bias + w].iter_mut().zip(dy) {
                    *slot += v as i128;
                }
                let mut dv = vec![0i64; f];
                transposed(&t[lv.ret..lv.ret + w * f], r[5], f, dy, MATERIAL_BITS, &mut dv)?;
                // The covectors of each drive's material part and of its bias: one covector a drive
                // except in the foil, whose material parts meet the other drive's bias alone.
                let times = |y: &[i32]| -> Result<Vec<i64>> { collect_exact(dv.iter().zip(y).map(|(&v, &y)| fit64(release(v as i128 * y as i128, FACE_BITS)))) };
                let (da, da_bias, db, db_bias) = match d.contact {
                    ContactLaw::Rectifying => {
                        let da: Vec<i64> = dv.iter().zip(&lc.drive).map(|(&v, &drive)| if drive > 0 { v } else { 0 }).collect();
                        (da.clone(), da, Vec::new(), Vec::new())
                    }
                    ContactLaw::Pair => {
                        let (da, db) = (times(&lc.pair)?, times(&lc.drive)?);
                        (da.clone(), da, db.clone(), db)
                    }
                    ContactLaw::PairLinear => {
                        (times(&t[lv.pair_bias..lv.pair_bias + f])?, times(&lc.pair)?, times(&t[lv.contact_bias..lv.contact_bias + f])?, times(&lc.drive)?)
                    }
                };
                for (slot, &v) in g[lv.contact_bias..lv.contact_bias + f].iter_mut().zip(&da_bias) {
                    *slot += v as i128;
                }
                let mut dr = vec![0i64; w];
                transposed(&t[lv.contact..lv.contact + f * w], r[4], w, &da, MATERIAL_BITS, &mut dr)?;
                if d.contact != ContactLaw::Rectifying {
                    for (slot, &v) in g[lv.pair_bias..lv.pair_bias + f].iter_mut().zip(&db_bias) {
                        *slot += v as i128;
                    }
                    let mut dr_b = vec![0i64; w];
                    transposed(&t[lv.pair..lv.pair + f * w], r[10], w, &db, MATERIAL_BITS, &mut dr_b)?;
                    for (a, b) in dr.iter_mut().zip(&dr_b) {
                        *a = fit64(*a as i128 + *b as i128)?;
                    }
                }
                let dread = ratio_adjoint(&lc.read, lc.read_scale, &dr)?;
                let neg: Vec<i64> = dread.iter().map(|v| -v).collect();
                let mut hre = vec![0i64; n];
                let mut him = vec![0i64; n];
                transposed(&t[lv.read_re..lv.read_re + w * n], r[2], n, &dread, MATERIAL_BITS, &mut hre)?;
                transposed(&t[lv.read_im..lv.read_im + w * n], r[3], n, &neg, MATERIAL_BITS, &mut him)?;
                read_cov.push(hre.into_iter().zip(him).collect());
                das.push(da);
                if d.contact != ContactLaw::Rectifying {
                    dbs.push(db);
                }
                dreads.push(dread);
                negs.push(neg);
            }
            let level = |i: usize| &cells[i].levels[l];
            let conducts: Vec<&[i32]> = (0..cells_n).map(|i| level(i).conduct.as_slice()).collect();
            let reads: Vec<&[i32]> = (0..cells_n).map(|i| level(i).read.as_slice()).collect();
            let faces_re: Vec<&[i64]> = (0..cells_n).map(|i| &level(i).state_face[..n]).collect();
            let faces_im: Vec<&[i64]> = (0..cells_n).map(|i| &level(i).state_face[n..]).collect();
            outer_sum(&mut g[lv.ret..lv.ret + w * f], f, &dx, &conducts)?;
            outer_sum(&mut g[lv.contact..lv.contact + f * w], w, &das, &reads)?;
            if d.contact != ContactLaw::Rectifying {
                outer_sum(&mut g[lv.pair..lv.pair + f * w], w, &dbs, &reads)?;
            }
            outer_sum(&mut g[lv.read_re..lv.read_re + w * n], n, &dreads, &faces_re)?;
            outer_sum(&mut g[lv.read_im..lv.read_im + w * n], n, &negs, &faces_im)?;
            // The reverse scan of the modes: G_h(t) = read covector + conj(λ_(t+1)) G_h(t+1)
            // (+ β_(t+1) conj(G_h(t+1)) when pumped).
            let mut carried: Vec<(i64, i64)> = vec![(0, 0); n];
            let mut gh_all: Vec<Vec<(i64, i64)>> = vec![Vec::new(); cells_n];
            for i in (0..cells_n).rev() {
                let mut gh = Vec::with_capacity(n);
                let later = if d.gated && i + 1 < cells_n { Some(&cells[i + 1].levels[l].gate) } else { None };
                for k in 0..n {
                    let (lr, li) = match later {
                        Some(gate) => (gate[k].lam.0 as i128, gate[k].lam.1 as i128),
                        None => (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128),
                    };
                    let (br, bi) = later.map_or((0, 0), |gate| (gate[k].beta.0 as i128, gate[k].beta.1 as i128));
                    let (cr, ci) = (carried[k].0 as i128, carried[k].1 as i128);
                    let re = fit64(read_cov[i][k].0 as i128 + release(lr * cr + li * ci + br * cr + bi * ci, MOVE_BITS))?;
                    let im = fit64(read_cov[i][k].1 as i128 + release(lr * ci - li * cr + bi * cr - br * ci, MOVE_BITS))?;
                    gh.push((re, im));
                }
                carried = gh.clone();
                gh_all[i] = gh;
            }
            let gammas = &reaches.gammas[l];
            // S_k = Σ_t Re(conj(G_h) B x): the covector of the mode's γ, on 2^(−48).
            let mut through_gamma = vec![0i128; n];
            // A gated level's covectors of |λ| and arg λ, on 2^(−48), and of each cell's gate.
            let mut along = vec![0i128; n];
            let mut around = vec![0i128; n];
            let mut dqs: Vec<Vec<i64>> = Vec::with_capacity(if d.gated { cells_n } else { 0 });
            let mut dss: Vec<Vec<i64>> = Vec::with_capacity(if d.turned { cells_n } else { 0 });
            let mut dks: Vec<Vec<i64>> = Vec::with_capacity(if d.pumped { cells_n } else { 0 });
            let mut dps: Vec<Vec<i64>> = Vec::with_capacity(if d.pumped { cells_n } else { 0 });
            let mut gres: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
            let mut gims: Vec<Vec<i64>> = Vec::with_capacity(cells_n);
            for (i, cell) in cells.iter().enumerate() {
                let lc = &cell.levels[l];
                let previous: &[(i64, i64)] = if i == 0 { &opening.modes[l] } else { &cells[i - 1].levels[l].state };
                let gh = &gh_all[i];
                let mut dq = vec![0i64; if d.gated { n } else { 0 }];
                let mut ds = vec![0i64; if d.turned { n } else { 0 }];
                let mut dk = vec![0i64; if d.pumped { n } else { 0 }];
                let mut dp = vec![0i64; if d.pumped { n } else { 0 }];
                for k in 0..n {
                    let (hr, hi) = (previous[k].0 as i128, previous[k].1 as i128);
                    let (gr, gi) = (gh[k].0 as i128, gh[k].1 as i128);
                    // conj(h_(t−1)) G_h(t), the covector of λ_t, and Re(conj(G_h) B x), of γ_t.
                    let (glr, gli) = (hr * gr + hi * gi, hr * gi - hi * gr);
                    let through = gr * lc.push[k].0 as i128 + gi * lc.push[k].1 as i128;
                    match lc.gate.get(k) {
                        None => {
                            g[lv.move_re + k] += glr;
                            g[lv.move_im + k] += gli;
                            through_gamma[k] += through;
                        }
                        Some(m) => {
                            let faces = &reaches.gates[l];
                            // Re(conj(i λ_t) G_λ): the covector of λ_t's turn, the founded turn's
                            // and, through ∂θ/∂s = π, the arriving symbol's.
                            let turning = release(m.lam.0 as i128 * gli - m.lam.1 as i128 * glr, MOVE_BITS);
                            around[k] += turning;
                            if d.turned {
                                ds[k] = fit64(release(reaches.half_turn * turning, MOVE_BITS + COVECTOR_BITS + turn_spread(w)))?;
                            }
                            // h_(t−1) G_h(t), the covector of β_t, on 2^(−48).
                            let (gbr, gbi) = (hr * gr - hi * gi, hr * gi + hi * gr);
                            let one = 1i128 << MOVE_BITS;
                            let (kappa, axis) = (m.kappa as i128, (m.axis.0 as i128, m.axis.1 as i128));
                            if d.pumped {
                                // Re(conj(iβ) G_β): the covector of the pump axis's turn, through ∂θ/∂p = π.
                                let axis_turning = release(m.beta.0 as i128 * gbi - m.beta.1 as i128 * gbr, MOVE_BITS);
                                dp[k] = fit64(release(reaches.half_turn * axis_turning, MOVE_BITS + COVECTOR_BITS + turn_spread(w)))?;
                                // −sgn(κ) Re(conj(ρU) G_α) + Re(conj(ρP) G_β), the covector of κ, on 2^(−48).
                                let rho = m.rho as i128;
                                let (vr, vi) = (release(rho * m.unit.0 as i128, MOVE_BITS), release(rho * m.unit.1 as i128, MOVE_BITS));
                                let (pr, pi) = (release(rho * axis.0, MOVE_BITS), release(rho * axis.1, MOVE_BITS));
                                let g_kappa = release(pr * gbr + pi * gbi - kappa.signum() * (vr * glr + vi * gli), MOVE_BITS);
                                // ∂κ/∂q = 2 ln 2 r (1 − r), on 2^(−30).
                                let open = m.pump_open as i128;
                                let f = release(release(ln2 * open, MOVE_BITS) * (one - open), MOVE_BITS);
                                dk[k] = fit64(release(g_kappa * 2 * f, COVECTOR_BITS + MOVE_BITS))?;
                            }
                            if !m.held {
                                // ∂α/∂ρ = (1 − |κ|) U and ∂β/∂ρ = κ P (U alone when unpumped).
                                let keep = one - kappa.abs();
                                let (ur, ui) = (release(keep * m.unit.0 as i128, MOVE_BITS), release(keep * m.unit.1 as i128, MOVE_BITS));
                                let (kr, ki) = (release(kappa * axis.0, MOVE_BITS), release(kappa * axis.1, MOVE_BITS));
                                let g_rho = release(ur * glr + ui * gli + kr * gbr + ki * gbi, MOVE_BITS) - div_nearest(m.rho as i128 * through, m.gamma as i128);
                                let (open, rho) = (m.open as i128, m.rho as i128);
                                along[k] += release(g_rho * div_nearest(GATE_REACH * open * rho, faces.moduli[k].max(1)), MOVE_BITS);
                                // ∂ρ_t/∂q = c ρ_t ℓ (ln 2)² r (1 − r), on 2^(−30).
                                let mut f = release(rho * faces.logs[k], MOVE_BITS);
                                f = release(f * ln2_square, MOVE_BITS);
                                f = release(f * open, MOVE_BITS);
                                f = release(f * ((1i128 << MOVE_BITS) - open), MOVE_BITS);
                                dq[k] = fit64(release(g_rho * GATE_REACH * f, COVECTOR_BITS + MOVE_BITS))?;
                            }
                        }
                    }
                }
                let gamma_at = |k: usize| lc.gate.get(k).map_or(gammas[k], |m| m.gamma as i128);
                let gre: Vec<i64> = collect_exact(gh.iter().enumerate().map(|(k, v)| fit64(release(gamma_at(k) * v.0 as i128, MOVE_BITS))))?;
                let gim: Vec<i64> = collect_exact(gh.iter().enumerate().map(|(k, v)| fit64(release(gamma_at(k) * v.1 as i128, MOVE_BITS))))?;
                let mut back_re = vec![0i64; w];
                let mut back_im = vec![0i64; w];
                transposed(&t[lv.push_re..lv.push_re + n * w], r[0], w, &gre, MATERIAL_BITS, &mut back_re)?;
                transposed(&t[lv.push_im..lv.push_im + n * w], r[1], w, &gim, MATERIAL_BITS, &mut back_im)?;
                let mut back_gate = vec![0i64; if d.gated { w } else { 0 }];
                if d.gated {
                    for (slot, &v) in g[lv.gate_bias..lv.gate_bias + n].iter_mut().zip(&dq) {
                        *slot += v as i128;
                    }
                    transposed(&t[lv.gate..lv.gate + n * w], r[6], w, &dq, MATERIAL_BITS, &mut back_gate)?;
                }
                let mut back_turn = vec![0i64; if d.turned { w } else { 0 }];
                if d.turned {
                    for (slot, &v) in g[lv.turn_bias..lv.turn_bias + n].iter_mut().zip(&ds) {
                        *slot += v as i128;
                    }
                    transposed(&t[lv.turn..lv.turn + n * w], r[7], w, &ds, MATERIAL_BITS, &mut back_turn)?;
                }
                let mut back_pump = vec![0i64; if d.pumped { w } else { 0 }];
                let mut back_axis = vec![0i64; if d.pumped { w } else { 0 }];
                if d.pumped {
                    for (slot, &v) in g[lv.pump_bias..lv.pump_bias + n].iter_mut().zip(&dk) {
                        *slot += v as i128;
                    }
                    transposed(&t[lv.pump..lv.pump + n * w], r[8], w, &dk, MATERIAL_BITS, &mut back_pump)?;
                    for (slot, &v) in g[lv.pump_axis_bias..lv.pump_axis_bias + n].iter_mut().zip(&dp) {
                        *slot += v as i128;
                    }
                    transposed(&t[lv.pump_axis..lv.pump_axis + n * w], r[9], w, &dp, MATERIAL_BITS, &mut back_axis)?;
                }
                let beside = |back: &[i64], j: usize| back.get(j).map_or(0, |&c| c as i128);
                let next: Vec<i64> = collect_exact(dx[i].iter().zip(back_re.iter().zip(&back_im)).enumerate().map(|(j, (v, (a, b)))| {
                    fit64(*v as i128 + *a as i128 + *b as i128 + beside(&back_gate, j) + beside(&back_turn, j) + beside(&back_pump, j) + beside(&back_axis, j))
                }))?;
                dx[i] = next;
                gres.push(gre);
                gims.push(gim);
                if d.gated {
                    dqs.push(dq);
                }
                if d.turned {
                    dss.push(ds);
                }
                if d.pumped {
                    dks.push(dk);
                    dps.push(dp);
                }
            }
            // The opening's credit: the covector reaching the carried state, a = conj(λ_0) G_h(0),
            // meets the moments its history carried (see [`LevelCredit`]).
            if let Some(credit) = opening.credit.as_ref().map(|c| &c[l]) {
                let first = &cells[0].levels[l];
                for k in 0..n {
                    let (lr, li) = match first.gate.get(k) {
                        Some(m) => (m.lam.0 as i128, m.lam.1 as i128),
                        None => (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128),
                    };
                    let (gr, gi) = (gh_all[0][k].0 as i128, gh_all[0][k].1 as i128);
                    let (ar, ai) = (release(lr * gr + li * gi, MOVE_BITS), release(lr * gi - li * gr, MOVE_BITS));
                    // Re(conj(a) z) and Re(conj(a) i z) of a moment z, on 2^(−48).
                    let real = |z: (i64, i64)| ar * z.0 as i128 + ai * z.1 as i128;
                    let turned = |z: (i64, i64)| ai * z.0 as i128 - ar * z.1 as i128;
                    for j in 0..w {
                        let p = credit.push[k * w + j];
                        g[lv.push_re + k * w + j] += release(real(p), STATE_BITS - FACE_BITS);
                        g[lv.push_im + k * w + j] += release(turned(p), STATE_BITS - FACE_BITS);
                    }
                    if d.gated {
                        along[k] += real(credit.along[k]);
                        around[k] += real(credit.around[k]);
                        g[lv.gate_bias + k] += release(real(credit.gate_bias[k]), COVECTOR_BITS);
                        for j in 0..w {
                            g[lv.gate + k * w + j] += release(real(credit.gate[k * w + j]), STATE_BITS - FACE_BITS);
                        }
                    } else {
                        // conj(A) a, the holomorphic part's covector, as the cells' conj(h) G_h.
                        let (sr, si) = (credit.along[k].0 as i128, credit.along[k].1 as i128);
                        g[lv.move_re + k] += sr * ar + si * ai;
                        g[lv.move_im + k] += sr * ai - si * ar;
                        through_gamma[k] += real(credit.around[k]);
                    }
                }
            }
            let inputs: Vec<&[i32]> = cells.iter().map(|cell| cell.levels[l].input.as_slice()).collect();
            outer_sum(&mut g[lv.push_re..lv.push_re + n * w], w, &gres, &inputs)?;
            outer_sum(&mut g[lv.push_im..lv.push_im + n * w], w, &gims, &inputs)?;
            if d.turned {
                outer_sum(&mut g[lv.turn..lv.turn + n * w], w, &dss, &inputs)?;
            }
            if d.pumped {
                outer_sum(&mut g[lv.pump..lv.pump + n * w], w, &dks, &inputs)?;
                outer_sum(&mut g[lv.pump_axis..lv.pump_axis + n * w], w, &dps, &inputs)?;
            }
            if d.gated {
                outer_sum(&mut g[lv.gate..lv.gate + n * w], w, &dqs, &inputs)?;
                // The Cartesian covector of the founded move: G_λ = u G_|λ| + i u G_φ/|λ|.
                let faces = &reaches.gates[l];
                for k in 0..n {
                    let (ur, ui) = faces.units[k];
                    let turn = div_nearest(around[k] << MOVE_BITS, faces.moduli[k].max(1));
                    g[lv.move_re + k] += release(ur * along[k] - ui * turn, MOVE_BITS);
                    g[lv.move_im + k] += release(ui * along[k] + ur * turn, MOVE_BITS);
                }
            } else {
                // ∂γ/∂λ = −λ/γ.
                for k in 0..n {
                    let (lr, li) = (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128);
                    g[lv.move_re + k] -= div_nearest(lr * through_gamma[k], gammas[k]);
                    g[lv.move_im + k] -= div_nearest(li * through_gamma[k], gammas[k]);
                }
            }
        }
        let e = self.layout.encoding;
        for (i, dxi) in dx.iter().enumerate() {
            let u = classes[i];
            for (slot, &v) in g[e + u * w..e + (u + 1) * w].iter_mut().zip(dxi) {
                *slot += v as i128;
            }
        }
        Ok(g)
    }

    /// Each level's credit moved through a section's cells (see [`LevelCredit`]): `cells` are this
    /// tower's forward from `opening`, so the moments follow the trajectory the stream continues on.
    ///
    /// The material moments `P` and `W` are linear in their drives, so a section moves them in one
    /// sum: with `π_s = λ_(T−1) ⋯ λ_(s+1)` the turn a cell's drive meets after it,
    /// `P_T = (λ_(T−1) ⋯ λ_0) P_0 + Σ_s π_s γ_s x_s` and `W_T = (λ_(T−1) ⋯ λ_0) W_0 + Σ_s π_s d_s x_s`,
    /// where `d_s = v_s ∂ρ_s/∂q` is the gate's drive (zero at a held cell). The per-mode moments
    /// keep the cell recursion.
    fn advance_credit(&self, credit: &mut [LevelCredit], opening: &TowerState, cells: &[Cell], reaches: &Reaches) -> Result<()> {
        let d = &self.declaration;
        let (w, n) = (d.width, d.modes);
        let t = &self.theta;
        let ln2_square = release(ln2_face() * ln2_face(), MOVE_BITS);
        let one = 1i128 << MOVE_BITS;
        let span = cells.len();
        if span == 0 {
            return Ok(());
        }
        let product = |a: (i128, i128), b: (i128, i128)| (release(a.0 * b.0 - a.1 * b.1, MOVE_BITS), release(a.0 * b.1 + a.1 * b.0, MOVE_BITS));
        for (l, lv) in self.layout.levels.iter().enumerate() {
            let c = &mut credit[l];
            let gated = !c.gate.is_empty();
            // Each cell's λ_t and γ_t on 2^(−30), and the gate's drive d_t on 2^(−24).
            let mut lams = vec![(0i128, 0i128); span * n];
            let mut gammas = vec![0i128; span * n];
            let mut drives = vec![(0i128, 0i128); if gated { span * n } else { 0 }];
            for (i, cell) in cells.iter().enumerate() {
                let lc = &cell.levels[l];
                let previous: &[(i64, i64)] = if i == 0 { &opening.modes[l] } else { &cells[i - 1].levels[l].state };
                for k in 0..n {
                    let (lr, li, gamma) = match lc.gate.get(k) {
                        Some(m) => (m.lam.0 as i128, m.lam.1 as i128, m.gamma as i128),
                        None => (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128, reaches.gammas[l][k]),
                    };
                    lams[i * n + k] = (lr, li);
                    gammas[i * n + k] = gamma;
                    // λ_t z, on z's grain.
                    let turn = |z: (i64, i64)| product((lr, li), (z.0 as i128, z.1 as i128));
                    let (hr, hi) = (previous[k].0 as i128, previous[k].1 as i128);
                    let (pr, pi) = (lc.push[k].0 as i128, lc.push[k].1 as i128);
                    let (ar, ai) = turn(c.along[k]);
                    let (kr, ki) = turn(c.around[k]);
                    let Some(m) = lc.gate.get(k) else {
                        c.along[k] = (fit64(ar + hr)?, fit64(ai + hi)?);
                        c.around[k] = (fit64(kr + pr)?, fit64(ki + pi)?);
                        continue;
                    };
                    // ∂h_t/∂φ = i λ_t h_(t−1).
                    let (turned_r, turned_i) = product((lr, li), (hr, hi));
                    c.around[k] = (fit64(kr - turned_i)?, fit64(ki + turned_r)?);
                    let (qr, qi) = turn(c.gate_bias[k]);
                    if m.held {
                        c.along[k] = (fit64(ar)?, fit64(ai)?);
                        c.gate_bias[k] = (fit64(qr)?, fit64(qi)?);
                        continue;
                    }
                    let faces = &reaches.gates[l];
                    let (ur, ui) = faces.units[k];
                    let (rho, open) = (m.rho as i128, m.open as i128);
                    // v = ∂h_t/∂ρ_t = u h_(t−1) − (ρ_t/γ_t) p_t, on 2^(−24).
                    let vr = release(ur * hr - ui * hi, MOVE_BITS) - div_nearest(rho * pr, gamma);
                    let vi = release(ur * hi + ui * hr, MOVE_BITS) - div_nearest(rho * pi, gamma);
                    // ∂ρ_t/∂|λ| = c r ρ_t/|λ| and ∂ρ_t/∂q = c ρ_t ℓ (ln 2)² r (1 − r), on 2^(−30).
                    let by_modulus = div_nearest(GATE_REACH * open * rho, faces.moduli[k].max(1));
                    let mut by_gate = release(rho * faces.logs[k], MOVE_BITS);
                    by_gate = release(by_gate * ln2_square, MOVE_BITS);
                    by_gate = release(by_gate * open, MOVE_BITS);
                    by_gate = GATE_REACH * release(by_gate * (one - open), MOVE_BITS);
                    c.along[k] = (fit64(ar + release(vr * by_modulus, MOVE_BITS))?, fit64(ai + release(vi * by_modulus, MOVE_BITS))?);
                    let (dr, di) = (release(vr * by_gate, MOVE_BITS), release(vi * by_gate, MOVE_BITS));
                    c.gate_bias[k] = (fit64(qr + dr)?, fit64(qi + di)?);
                    drives[i * n + k] = (dr, di);
                }
            }
            // π_s, the turn after cell s, and the whole section's turn λ_(T−1) ⋯ λ_0.
            let mut after = vec![(0i128, 0i128); span * n];
            for k in 0..n {
                after[(span - 1) * n + k] = (one, 0);
            }
            for s in (0..span - 1).rev() {
                for k in 0..n {
                    after[s * n + k] = product(after[(s + 1) * n + k], lams[(s + 1) * n + k]);
                }
            }
            let whole: Vec<(i128, i128)> = (0..n).map(|k| product(after[k], lams[k])).collect();
            let inputs: Vec<&[i32]> = cells.iter().map(|cell| cell.levels[l].input.as_slice()).collect();
            // One family's moments `M_T = whole · M_0 + release(Σ_s coefficient_s ⊗ x_s)`, the
            // coefficients interleaved (re, im) a mode.
            let mut moved = |moments: &mut [(i64, i64)], coefficients: &[Vec<i64>], shift: u32| -> Result<()> {
                let mut sum = vec![0i128; 2 * n * w];
                outer_sum(&mut sum, w, coefficients, &inputs)?;
                for k in 0..n {
                    for j in 0..w {
                        let z = moments[k * w + j];
                        let (er, ei) = product(whole[k], (z.0 as i128, z.1 as i128));
                        moments[k * w + j] = (fit64(er + release(sum[2 * k * w + j], shift))?, fit64(ei + release(sum[(2 * k + 1) * w + j], shift))?);
                    }
                }
                Ok(())
            };
            // The push's coefficient π_s γ_s on 2^(−30); γ x on 2^(−46) releases to the state's grain.
            let pushes = (0..span)
                .map(|s| {
                    (0..n)
                        .flat_map(|k| {
                            let (pr, pi) = after[s * n + k];
                            let g = gammas[s * n + k];
                            [release(pr * g, MOVE_BITS), release(pi * g, MOVE_BITS)]
                        })
                        .map(fit64)
                        .collect::<Result<Vec<_>>>()
                })
                .collect::<Result<Vec<_>>>()?;
            moved(&mut c.push, &pushes, MOVE_BITS + FACE_BITS - STATE_BITS)?;
            if gated {
                // The gate's coefficient π_s d_s on 2^(−24); d x on 2^(−40) releases to 2^(−24).
                let gates = (0..span)
                    .map(|s| {
                        (0..n)
                            .flat_map(|k| {
                                let (gr, gi) = product(after[s * n + k], drives[s * n + k]);
                                [gr, gi]
                            })
                            .map(fit64)
                            .collect::<Result<Vec<_>>>()
                    })
                    .collect::<Result<Vec<_>>>()?;
                moved(&mut c.gate, &gates, FACE_BITS)?;
            }
        }
        Ok(())
    }

    /// Every stream's continuing state from its section's forward, its credit moved along it.
    fn carry_credit(&self, states: &mut [TowerState], ends: Vec<(Vec<Cell>, TowerState)>, opening: &[TowerState], reaches: &Reaches) -> Result<()> {
        if self.declaration.turned && ends.iter().any(|(_, end)| end.credit.is_some()) {
            return refuse("the passage credit does not carry a turned mode");
        }
        states.par_iter_mut().zip(ends.into_par_iter()).zip(opening.par_iter()).try_for_each(|((s, (cells, mut end)), open)| {
            if let Some(credit) = end.credit.as_mut() {
                self.advance_credit(credit, open, &cells, reaches)?;
            }
            *s = end;
            Ok(())
        })
    }

    /// The covector on the deposit's grain `2^(−32)` from each family's natural grain.
    fn to_step_grain(&self, g: &mut [i128]) {
        for lv in &self.layout.levels {
            for k in [lv.move_re, lv.move_im] {
                for v in &mut g[k..k + self.declaration.modes] {
                    *v = release(*v, 2 * COVECTOR_BITS - STEP_BITS);
                }
            }
        }
        for &(start, len, grain) in &self.layout.families {
            if grain == MOVE_BITS {
                continue;
            }
            for v in &mut g[start..start + len] {
                *v = if grain == MATERIAL_BITS {
                    release(*v, COVECTOR_BITS + FACE_BITS - STEP_BITS)
                } else {
                    *v << (STEP_BITS - COVECTOR_BITS)
                };
            }
        }
    }

    /// The material as text.
    pub fn to_text(&self) -> String {
        let d = &self.declaration;
        let gated = if d.gated { " gated" } else { "" };
        let turned = if d.turned { " turned" } else { "" };
        let pumped = if d.pumped { " pumped" } else { "" };
        let contact = match d.contact {
            ContactLaw::Rectifying => "",
            ContactLaw::Pair => " pair",
            ContactLaw::PairLinear => " pair-linear",
        };
        let mut s = format!("moment-tower-v1 {} {} {} {} {}{gated}{turned}{pumped}{contact}\n", d.alphabet, d.width, d.modes, d.contacts, d.levels);
        s.push_str(&self.theta.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    /// The material from its text, refused unless it restores whole.
    pub fn from_text(text: &str) -> Result<Self> {
        let mut lines = text.lines();
        let head: Vec<&str> = lines.next().unwrap_or("").split(' ').collect();
        if head.len() < 6 || head[0] != "moment-tower-v1" {
            return refuse("not a moment tower's text");
        }
        // The mode laws in their order (`gated`, `turned`, `pumped`), then the contact law.
        let (modes, contact) = match head[6..].split_last() {
            Some((&"pair", modes)) => (modes, ContactLaw::Pair),
            Some((&"pair-linear", modes)) => (modes, ContactLaw::PairLinear),
            _ => (&head[6..], ContactLaw::Rectifying),
        };
        if modes.len() > 3 || modes != &["gated", "turned", "pumped"][..modes.len()] {
            return refuse("not a moment tower's text");
        }
        let (gated, turned, pumped) = (!modes.is_empty(), modes.len() >= 2, modes.len() == 3);
        let num = |s: &str| s.parse::<usize>().map_err(|_| TowerError::Refused("a declaration that is not a count"));
        let declaration = TowerDeclaration {
            alphabet: num(head[1])?,
            width: num(head[2])?,
            modes: num(head[3])?,
            contacts: num(head[4])?,
            levels: num(head[5])?,
            gated,
            turned,
            pumped,
            contact,
        };
        let layout = Layout::new(&declaration);
        let theta: Vec<i32> = lines
            .next()
            .unwrap_or("")
            .split(' ')
            .map(|s| s.parse::<i32>().map_err(|_| TowerError::Refused("material that is not an integer")))
            .collect::<Result<_>>()?;
        if theta.len() != layout.len || lines.next().is_some() {
            return refuse("material of the wrong extent");
        }
        Ok(Self { declaration, theta, layout, exponential: Exponential::new(FACE_BITS), fine: Exponential::new(MOVE_BITS) })
    }
}

/// The turn ladder's count `J` for `N` modes: the largest power of two up to eight that divides
/// `N` (agent-inferred: eight turns of the half circle when the bank allows); the scale ladder has
/// `N/J` rungs.
fn turn_ladder(modes: usize) -> usize {
    let mut turns = 1usize;
    while turns < 8 && modes % (turns * 2) == 0 {
        turns *= 2;
    }
    turns
}

/// The exact comparison of two sections' codes: does `new` code strictly fewer bits than `old`?
/// `Π p_new > Π p_old`, over the products of their faces' numerators and denominators.
fn fewer_bits(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    fn product(v: &[u128]) -> BigUint {
        match v.len() {
            0 => BigUint::from(1u8),
            1 => BigUint::from(v[0]),
            n => product(&v[..n / 2]) * product(&v[n / 2..]),
        }
    }
    let (om, ot): (Vec<u128>, Vec<u128>) = old.iter().cloned().unzip();
    let (nm, nt): (Vec<u128>, Vec<u128>) = new.iter().cloned().unzip();
    product(&nm) * product(&ot) > product(&om) * product(&nt)
}

/// A moment moved toward its input at the rate `2^(−rate)`: `m + release(g − m, rate)`, and at
/// least one grain when that release rounds to zero. Released to the nearest grain alone, a moment
/// within `2^(rate−1)` grains of its input never reaches it, so a contact that stops conducting
/// keeps its last moments (`|m| ≤ 3`, `v ≤ 127` grains) and the step `m/(√v + 2^(−32))` reads that
/// remainder as a covector of a quarter of the rate (measured October 23 on all 6,726 GSM8K
/// problems, the narrow tower: no weight stalled through pass 2; 980 had by pass 3 and 2,146 by
/// pass 4, the most of two contacts that had stopped conducting, each moving `2^(−9)` every section,
/// one from 0.64 at pass 2 to 15.9 at pass 5). A silent contact's drifted weights meet the residual
/// stream at full scale when it conducts again. Moved by a grain, the moment reaches its input.
fn toward(m: i128, g: i128, rate: u32) -> i128 {
    let step = release(g - m, rate);
    m + if step == 0 { (g - m).signum() } else { step }
}

/// [definition; agent-inferred] **The learner**: the tower, the covector's moments and the
/// deposits' receipts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerLearner {
    pub tower: Tower,
    first: Vec<i128>,
    second: Vec<i128>,
    opened: bool,
    /// The step's rate, `2^(−k)`.
    pub rate_bits: u32,
    /// The last section's swell per level, on `2^(−16)`: `max |x|`, `max |h|` (its face), `max
    /// ‖r‖_rms`, `max |W₁ r̂ + b₁|` (and the pair contact's second drive) over every stream's cells.
    /// A reading for the receipt, not material.
    pub swell: Vec<[u64; 4]>,
}

/// A section's receipt: its code before and after (on `2^(−20)` bits), the halvings the
/// certificate took, and whether a deposit was admitted; and each part's code before and after,
/// in the order the parts were given (after is before where nothing was deposited). The
/// certificate admits a step on the parts' summed covector when the whole code falls, so one part's
/// code can rise under a step the others pay for: the parts' codes read whether they do.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionReceipt {
    pub cells: usize,
    pub code_before: i64,
    pub code_after: i64,
    pub halvings: u32,
    pub deposited: bool,
    pub parts: Vec<(i64, i64)>,
}

impl TowerLearner {
    pub fn new(tower: Tower, rate_bits: u32) -> Self {
        let len = tower.theta.len();
        Self { tower, first: vec![0; len], second: vec![0; len], opened: false, rate_bits, swell: Vec::new() }
    }

    /// The swell and the reaches as one line: per level `x h r a` (faces, `2^(−16)`) and `push read
    /// contact return` (material, `2^(−24)`), then the readout's reach and `max |λ|` on `2^(−30)`.
    pub fn swell_line(&self) -> String {
        let reaches = self.tower.reaches();
        let mut line = String::new();
        for (l, r) in reaches.levels.iter().enumerate() {
            let s = self.swell.get(l).copied().unwrap_or([0; 4]);
            let lv = self.tower.layout.levels[l];
            let lambda = (0..self.tower.declaration.modes)
                .map(|k| {
                    let (re, im) = (self.tower.theta[lv.move_re + k] as i128, self.tower.theta[lv.move_im + k] as i128);
                    ((re * re + im * im) as u128).isqrt()
                })
                .max()
                .unwrap_or(0);
            let pair = if self.tower.declaration.contact == ContactLaw::Rectifying { String::new() } else { format!(" pair={}", r[10]) };
            line.push_str(&format!(
                "L{l} x={} h={} r={} a={} push={} read={} contact={}{pair} return={} lambda={} ",
                s[0], s[1], s[2], s[3], r[0].max(r[1]), r[2].max(r[3]), r[4], r[5], lambda
            ));
        }
        line.push_str(&format!("readout={}", reaches.readout));
        line
    }

    /// One section over parallel streams: each stream's classes `[0..=T]` from its carried state.
    /// The streams' covectors are summed, the moments move, the step is certified by the reread,
    /// and each stream's state continues under the material the section ends with.
    pub fn section(&mut self, states: &mut [TowerState], classes: &[&[usize]]) -> Result<SectionReceipt> {
        self.section_compared(states, classes, None)
    }

    /// A section whose comparison is declared place by place (`reverse_joined`): each face is
    /// compared with the class `compared` names there, or with nothing where the class read is
    /// the tower's own release re-entering. A place compared with nothing sends no covector and
    /// neither the code nor the certificate counts it; the code and the certificate read every
    /// other face at its declared class.
    pub fn section_compared(&mut self, states: &mut [TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>) -> Result<SectionReceipt> {
        if states.len() != classes.len() || classes.iter().any(|c| c.len() < 2) {
            return refuse("a section needs one carried state and two classes a stream");
        }
        if compared.is_some_and(|m| m.len() != classes.len() || m.iter().zip(classes).any(|(m, c)| m.len() != c.len())) {
            return refuse("a comparison for each class of each stream");
        }
        let target = |s: usize, i: usize| compared.map_or(Some(classes[s][i]), |m| m[s][i]);
        let tower = &self.tower;
        let reaches = tower.reaches();
        let opening: Vec<TowerState> = states.to_vec();
        let forwards: Vec<(Vec<Cell>, TowerState)> = opening
            .par_iter()
            .zip(classes.par_iter())
            .map(|(open, c)| {
                let mut s = open.clone();
                let cells = tower.forward(&mut s, c, &reaches)?;
                Ok((cells, s))
            })
            .collect::<Result<_>>()?;
        self.swell = (0..tower.declaration.levels)
            .map(|l| {
                let mut m = [0u64; 4];
                for lc in forwards.iter().flat_map(|(cells, _)| cells.iter().map(move |c| &c.levels[l])) {
                    m[0] = m[0].max(reach(&lc.input));
                    m[1] = m[1].max(reach64(&lc.state_face));
                    m[2] = m[2].max(lc.read_scale as u64);
                    m[3] = m[3].max(reach(&lc.drive)).max(reach(&lc.pair));
                }
                m
            })
            .collect();
        let faces_old: Vec<(u128, u128)> = forwards
            .iter()
            .enumerate()
            .flat_map(|(s, (cells, _))| cells.iter().enumerate().filter_map(move |(i, cell)| target(s, i + 1).map(|t| (cell.face.masses[t], cell.face.total))))
            .collect();
        let part_codes = |passes: &[(Vec<Cell>, TowerState)]| -> Vec<i64> {
            passes
                .iter()
                .enumerate()
                .map(|(s, (cells, _))| cells.iter().enumerate().filter_map(|(i, cell)| target(s, i + 1).map(|t| cell.face.code(t))).sum::<i64>())
                .collect()
        };
        let parts_before = part_codes(&forwards);
        let code_before: i64 = parts_before.iter().sum();
        let gradients: Vec<Vec<i128>> = opening
            .par_iter()
            .zip(forwards.par_iter())
            .zip(classes.par_iter())
            .enumerate()
            .map(|(s, ((open, (cells, _)), c))| tower.reverse(open, cells, c, compared.map(|m| m[s])))
            .collect::<Result<_>>()?;
        let mut g = vec![0i128; tower.theta.len()];
        for gs in &gradients {
            for (a, b) in g.iter_mut().zip(gs) {
                *a += *b;
            }
        }
        tower.to_step_grain(&mut g);
        tower.to_move_chart(&mut g);
        // The moments.
        if !self.opened {
            self.first.clone_from(&g);
            self.second = g
                .iter()
                .map(|v| v.checked_mul(*v).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier")))
                .collect::<Result<_>>()?;
            self.opened = true;
        } else {
            for ((m, v), gv) in self.first.iter_mut().zip(self.second.iter_mut()).zip(&g) {
                let square = gv.checked_mul(*gv).ok_or(TowerError::Refused("a covector's square outgrew its 128-bit carrier"))?;
                *m = toward(*m, *gv, FIRST_RATE);
                *v = toward(*v, square, SECOND_RATE);
            }
        }
        // The proposed step on each family's grain.
        let mut step = vec![0i128; g.len()];
        for &(start, len, grain) in &self.tower.layout.families {
            for i in start..start + len {
                let root = (self.second[i].max(0) as u128).isqrt() as i128 + 1;
                let num = self.first[i] << grain;
                let q = (num >> self.rate_bits) / root;
                step[i] = q;
            }
        }
        // The certificate halves a refused step until it is certified or has released below every
        // family's grain; then the section deposits nothing.
        let mut halvings = 0u32;
        loop {
            let mut candidate = self.tower.clone();
            let mut moved = false;
            for &(start, len, grain) in &self.tower.layout.families {
                if grain == MOVE_BITS {
                    continue;
                }
                for i in start..start + len {
                    let released = release(step[i], halvings);
                    moved |= released != 0;
                    candidate.theta[i] = fit32(candidate.theta[i] as i128 - released, "a deposited parameter outgrew its 32-bit carrier")?;
                }
            }
            moved |= candidate.move_by_chart(&step, halvings)?;
            if !moved {
                self.tower.carry_credit(states, forwards, &opening, &reaches)?;
                let parts = parts_before.iter().map(|&c| (c, c)).collect();
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after: code_before, halvings, deposited: false, parts });
            }
            candidate.project();
            let creaches = candidate.reaches();
            let rereads: Vec<(Vec<Cell>, TowerState)> = opening
                .par_iter()
                .zip(classes.par_iter())
                .map(|(open, c)| {
                    let mut s = open.clone();
                    let cells = candidate.forward(&mut s, c, &creaches)?;
                    Ok((cells, s))
                })
                .collect::<Result<_>>()?;
            let faces_new: Vec<(u128, u128)> = rereads
                .iter()
                .enumerate()
                .flat_map(|(s, (cells, _))| cells.iter().enumerate().filter_map(move |(i, cell)| target(s, i + 1).map(|t| (cell.face.masses[t], cell.face.total))))
                .collect();
            if fewer_bits(&faces_old, &faces_new) {
                let parts_after = part_codes(&rereads);
                let code_after: i64 = parts_after.iter().sum();
                let parts = parts_before.iter().copied().zip(parts_after).collect();
                candidate.carry_credit(states, rereads, &opening, &creaches)?;
                self.tower = candidate;
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after, halvings, deposited: true, parts });
            }
            halvings += 1;
        }
    }

    /// The learner as text: the tower, then the moments.
    pub fn to_text(&self) -> String {
        let mut s = self.tower.to_text();
        s.push_str(&format!("moments {} {}\n", self.rate_bits, self.opened as u8));
        s.push_str(&self.first.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s.push_str(&self.second.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
        s.push('\n');
        s
    }

    pub fn from_text(text: &str) -> Result<Self> {
        let lines: Vec<&str> = text.lines().collect();
        if lines.len() != 5 {
            return refuse("a learner's text has five lines");
        }
        let tower = Tower::from_text(&format!("{}\n{}\n", lines[0], lines[1]))?;
        let head: Vec<&str> = lines[2].split(' ').collect();
        if head.len() != 3 || head[0] != "moments" {
            return refuse("not a learner's moments");
        }
        let rate_bits = head[1].parse::<u32>().map_err(|_| TowerError::Refused("a rate that is not a count"))?;
        let opened = head[2] == "1";
        let parse = |l: &str| -> Result<Vec<i128>> {
            l.split(' ').map(|s| s.parse::<i128>().map_err(|_| TowerError::Refused("a moment that is not an integer"))).collect()
        };
        let first = parse(lines[3])?;
        let second = parse(lines[4])?;
        if first.len() != tower.theta.len() || second.len() != tower.theta.len() {
            return refuse("moments of the wrong extent");
        }
        Ok(Self { tower, first, second, opened, rate_bits, swell: Vec::new() })
    }
}

impl Tower {
    /// [definition; agent-inferred, October 23] **A move's deposit chart.** A move `λ = ρ e^(iφ)`
    /// is stepped in `(ν, φ)` with `ν = ln(1 − ρ)`: the logarithm of its distance to the unit
    /// circle (to first order its dissipation a tick) and its turn. A Cartesian step of the rate
    /// `2^(−7)` moves `ρ` by up to 0.008 a section, so it crosses the 0.026 between `ρ = 0.974` and
    /// the margin in about three (measured, second pass on 1,000 GSM8K problems: `ρ` went from 0.974
    /// to 0.991 in nine sections and the state's face five-fold, then past its carrier); in the
    /// chart a step changes `1 − ρ` by the factor `e^(±2^(−k))`. The covector on `2^(−32)` becomes
    /// `g_ν = −(1 − ρ) ⟨λ/ρ, g⟩`, `g_φ = λ_re g_im − λ_im g_re`; at `ρ = 0` the chart's direction is
    /// the real axis.
    fn to_move_chart(&self, g: &mut [i128]) {
        let one = 1i128 << MOVE_BITS;
        for lv in &self.layout.levels {
            for k in 0..self.declaration.modes {
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let (gr, gi) = (g[lv.move_re + k], g[lv.move_im + k]);
                let (modulus, _) = modulus_and_gamma(re, im);
                let radial = if modulus == 0 { gr } else { div_nearest(re * gr + im * gi, modulus) };
                g[lv.move_re + k] = -release((one - modulus) * radial, MOVE_BITS);
                g[lv.move_im + k] = release(re * gi - im * gr, MOVE_BITS);
            }
        }
    }

    /// Every move stepped in its chart by `(Δν, Δφ)` released `halvings` coarser: `1 − ρ ← (1 − ρ)
    /// e^(−Δν)`, `φ ← φ − Δφ`, then projected inside the margin. Whether any move moved.
    fn move_by_chart(&mut self, step: &[i128], halvings: u32) -> Result<bool> {
        let one = 1i128 << MOVE_BITS;
        let mut moved = false;
        for lv in self.layout.levels.clone() {
            for k in 0..self.declaration.modes {
                let dn = release(step[lv.move_re + k], halvings);
                let dp = release(step[lv.move_im + k], halvings);
                if dn == 0 && dp == 0 {
                    continue;
                }
                moved = true;
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let (modulus, _) = modulus_and_gamma(re, im);
                let distance = release((one - modulus) * exp_series(-dn, 0).0, MOVE_BITS);
                let target = one - distance;
                let unit = if modulus == 0 { (one, 0) } else { (div_nearest(re * one, modulus), div_nearest(im * one, modulus)) };
                let (c, sn) = exp_series(0, -dp);
                let ur = release(unit.0 * c - unit.1 * sn, MOVE_BITS);
                let ui = release(unit.0 * sn + unit.1 * c, MOVE_BITS);
                self.theta[lv.move_re + k] = fit32(release(target * ur, MOVE_BITS), "a deposited move outgrew its 32-bit carrier")?;
                self.theta[lv.move_im + k] = fit32(release(target * ui, MOVE_BITS), "a deposited move outgrew its 32-bit carrier")?;
            }
        }
        Ok(moved)
    }

    /// Every move back inside its disk, `|λ| ≤ 1 − 2^(−12)`.
    fn project(&mut self) {
        let radius = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - MARGIN));
        for lv in self.layout.levels.clone() {
            for k in 0..self.declaration.modes {
                let (re, im) = (self.theta[lv.move_re + k] as i128, self.theta[lv.move_im + k] as i128);
                let n = re * re + im * im;
                if n > radius * radius {
                    let modulus = (n as u128).isqrt() as i128 + 1;
                    self.theta[lv.move_re + k] = (re * radius / modulus) as i32;
                    self.theta[lv.move_im + k] = (im * radius / modulus) as i32;
                }
            }
        }
    }

    /// A frozen reading: the code of `classes[1..]` from the state, on `2^(−20)` bits, the state
    /// moved.
    pub fn read(&self, state: &mut TowerState, classes: &[usize]) -> Result<i64> {
        Ok(self.read_cells(state, classes)?.iter().sum())
    }

    /// Each cell's code: entry `i` is the face after `classes[i]` read at `classes[i + 1]`, on
    /// `2^(−READ_BITS)` bits, so a receiver can sum it over any partition of the passage.
    pub fn read_cells(&self, state: &mut TowerState, classes: &[usize]) -> Result<Vec<i64>> {
        let reaches = self.reaches();
        let mut codes = Vec::with_capacity(classes.len().saturating_sub(1));
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            codes.push(cell.face.code(classes[i + 1]));
        }
        Ok(codes)
    }

    /// The class's face `E(u)`, the encoding the bottom level reads (`x⁰_t = E(u_t)`), on
    /// `2^(−16)`.
    pub fn encoding(&self, u: usize) -> &[i32] {
        let w = self.declaration.width;
        let e = self.layout.encoding + u * w;
        &self.theta[e..e + w]
    }

    /// [agent-inferred with the mathematics thread, October 24] **The tension reading**: the
    /// frozen tower reads `classes` from the state, and each cell's [`TensionCell`] (its face
    /// compared with the class that arrives next) is handed to `each`. A reading beside the code:
    /// the tower is not moved, and the receiver keeps only the three moment sums, never the cells.
    pub fn read_tension(&self, state: &mut TowerState, classes: &[usize], mut each: impl FnMut(TensionCell) -> Result<()>) -> Result<()> {
        let reaches = self.reaches();
        let (w, n) = (self.declaration.width, self.declaration.modes);
        let top_level = self.layout.levels.len() - 1;
        let lv = &self.layout.levels[top_level];
        let r = &reaches.levels[top_level];
        let t = &self.theta;
        let mut a = vec![0i64; w];
        let mut b = vec![0i64; w];
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            let level = &cell.levels[top_level];
            let face = &level.state_face;
            // Im(C h) = C_re h_im + C_im h_re, on 2^(−40) released to 2^(−16), then read on the
            // read's ratio: only the read's ratio reaches the contacts.
            affine(&t[lv.read_re..lv.read_re + w * n], r[2], n, &face[n..], None, 0, 0, &mut a)?;
            affine(&t[lv.read_im..lv.read_im + w * n], r[3], n, &face[..n], None, 0, 0, &mut b)?;
            let quadrature = collect_exact(a.iter().zip(&b).map(|(x, y)| {
                let raw = release(*x as i128 + *y as i128, MATERIAL_BITS);
                if level.read_scale == 0 { Ok(0) } else { fit32(div_nearest(raw << FACE_BITS, level.read_scale), "a quadrature's ratio outgrew its 32-bit carrier") }
            }))?;
            let below = level.input.clone();
            each(TensionCell { covector: covector(&cell.face, classes[i + 1]), quadrature, below, top: cell.top })?;
        }
        Ok(())
    }

    /// [agent-inferred, October 24] **The faces a joined face reads**: the frozen tower reads
    /// `classes` from the state, and each cell's index, top face (what the readout reads) and face
    /// (the masses of the class that arrives next) are handed to `each`. A reading beside the code:
    /// the tower is not moved, and the receiver keeps what it joins, never the cells.
    pub fn read_faces(&self, state: &mut TowerState, classes: &[usize], mut each: impl FnMut(usize, &[i32], &TowerFace) -> Result<()>) -> Result<()> {
        let reaches = self.reaches();
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            each(i, &cell.top, &cell.face)?;
        }
        Ok(())
    }

    /// [definition; agent-inferred with the mathematics thread, October 24] **Where the pair
    /// contact's bilinear weight sits.** Each level's drives read back onto the modes' faces,
    /// `A = W_a [C_re, −C_im]` and `B = W_b [C_re, −C_im]` (the read is `Re(C h)`, so a mode
    /// enters through its in-phase and quadrature parts), give contact `o`'s bilinear block the
    /// coefficient `A_(o,k) B_(o,k′)` on the product of modes `k` and `k′`. Its weight on the
    /// founded memory rungs `(s, s′)` of the two modes (`|λ| = 1 − 2^(−s−1)` at founding, the
    /// scale ladder's rung, the margin's rung shared past it) is
    ///
    /// ```text
    /// E_(s,s′) = Σ_o (Σ_(k on s) |A_(o,k)|²) (Σ_(k′ on s′) |B_(o,k′)|²)
    /// ```
    ///
    /// with each coefficient released to `2^(−24)` before it is squared, so `E` is on `2^(−96)`.
    /// Rung `s` is the first drive's (rows), `s′` the second's (columns). The mathematics thread's
    /// cycles record reads the slip's split through it: a held rung against a fast one is the
    /// harmonic part (a cycle no local cell bounds, which retention keeps), fast against fast
    /// the coexact (a local curl). An exterior reading of the material: the tower is not moved. A
    /// rectifying tower has no bilinear block (a typed refusal).
    pub fn bilinear_rungs(&self) -> Result<Vec<Vec<Vec<BigUint>>>> {
        let d = &self.declaration;
        if d.contact == ContactLaw::Rectifying {
            return refuse("a rectifying contact has no bilinear block");
        }
        let (w, n, f) = (d.width, d.modes, d.contacts);
        let turns = turn_ladder(n);
        let rung = |k: usize| (k / turns).min(MARGIN as usize - 1);
        let rungs = rung(n - 1) + 1;
        let t = &self.theta;
        let mut levels = Vec::with_capacity(self.layout.levels.len());
        for lv in &self.layout.levels {
            // Σ over a rung of |drive read back onto mode k|², per contact, on 2^(−48).
            let on_rungs = |material: usize| -> Vec<Vec<u128>> {
                (0..f)
                    .map(|o| {
                        let mut e = vec![0u128; rungs];
                        for k in 0..n {
                            let (mut re, mut im) = (0i128, 0i128);
                            for i in 0..w {
                                let m = t[material + o * w + i] as i128;
                                re += m * t[lv.read_re + i * n + k] as i128;
                                im += m * t[lv.read_im + i * n + k] as i128;
                            }
                            let (re, im) = (release(re, MATERIAL_BITS).unsigned_abs(), release(im, MATERIAL_BITS).unsigned_abs());
                            e[rung(k)] += re * re + im * im;
                        }
                        e
                    })
                    .collect()
            };
            let (a, b) = (on_rungs(lv.contact), on_rungs(lv.pair));
            let mut e = vec![vec![BigUint::from(0u32); rungs]; rungs];
            for (ao, bo) in a.iter().zip(&b) {
                for (s, &x) in ao.iter().enumerate() {
                    for (s2, &y) in bo.iter().enumerate() {
                        e[s][s2] += BigUint::from(x) * BigUint::from(y);
                    }
                }
            }
            levels.push(e);
        }
        Ok(levels)
    }
}

/// [definition; agent-inferred, October 23] **The tower joined to a cell-grain face.** The route
/// (`hnn::keyed_modes`) reads base-four cells; the tower reads bytes. At a cell of phase `k` the
/// tower's face is its byte face summed over the cell's prefix ([`TowerFace::cell_masses`]), and
/// its news over the route's face `r` is `f_d = log₂ t̂(d) − log₂ r̂(d)`. The joined face is
///
/// ```text
/// p̂(d) ∝ r_d 2^(α_k f_d)            (= r̂^(1−α) t̂^α: the geometric join of the two faces)
/// ```
///
/// with one weight per phase on `2^(−16)`, opened at `½` (no evidence favours either face). The
/// weight's covector at a cell is `E_p̂[f] − f_actual` bits and its curvature `ln 2 · Var_p̂(f)`;
/// a section closes with the lock's Newton step on its cumulative curvature from a prior of one,
/// `α ← α − G / (ln 2 (1 + Σ C))`, projected into `|α| ≤ 2^4`. The code is convex in `α`, so
/// the step descends (the lock's certificate, `hnn::keyed_modes`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellJoin {
    /// `α_k` on `2^(−16)`.
    pub weights: [i64; 4],
    /// The section's covector per phase on `2^(−20)` bits.
    gradient: [i128; 4],
    /// The cumulative curvature per phase on `2^(−40)`, the prior `2^40` included.
    curvature: [i128; 4],
    exponential: Exponential,
}

/// The join's weight grain, `2^(−16)`.
pub const JOIN_BITS: u32 = 16;
/// The join's weight reach, `|α| ≤ 2^4`.
const JOIN_REACH: i64 = 1 << (JOIN_BITS + 4);

/// One joined cell: the joined face, and the news it was read with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinedCell {
    pub masses: [u128; 4],
    pub total: u128,
    /// `f_d` on `2^(−20)` bits.
    pub news: [i64; 4],
}

impl JoinedCell {
    /// `−log₂ p̂(d)` on `2^(−20)` bits.
    pub fn code(&self, d: usize) -> i64 {
        code_of(self.masses[d], self.total)
    }
}

/// `m / t` on `2^(−62)`, at least one grain; a total past `2^64` is re-based so the shift fits.
pub fn unit_of(m: u128, t: u128) -> u128 {
    let shift = (128 - t.leading_zeros()).saturating_sub(64);
    (((m >> shift) << UNIT_BITS) / (t >> shift).max(1)).clamp(1, 1u128 << UNIT_BITS)
}

/// `−log₂(m / t)` on `2^(−20)` bits, for any face's mass and total.
pub fn code_of(m: u128, t: u128) -> i64 {
    -(log2_face(unit_of(m, t), READ_BITS) as i64)
}

impl Default for CellJoin {
    fn default() -> Self {
        Self::new([1 << (JOIN_BITS - 1); 4])
    }
}

impl CellJoin {
    pub fn new(weights: [i64; 4]) -> Self {
        Self { weights, gradient: [0; 4], curvature: [1i128 << 40; 4], exponential: Exponential::new(JOIN_BITS) }
    }

    /// The joined face at a cell of `phase`, from the route's masses and the tower's cell masses.
    pub fn face(&self, route: &[u128], tower: &[u128; 4], phase: usize) -> Result<JoinedCell> {
        if route.len() != 4 || phase > 3 {
            return refuse("a joined cell has four classes and a phase below four");
        }
        let rt: u128 = route.iter().sum();
        let tt: u128 = tower.iter().sum();
        if rt == 0 || tt == 0 {
            return refuse("a joined cell needs both faces with mass");
        }
        let unit = unit_of;
        let mut news = [0i64; 4];
        for d in 0..4 {
            news[d] = (log2_face(unit(tower[d], tt), READ_BITS) - log2_face(unit(route[d], rt), READ_BITS)) as i64;
        }
        let alpha = self.weights[phase] as i128;
        let w: Vec<i128> = news.iter().map(|&f| release(alpha * f as i128, READ_BITS)).collect();
        let top = *w.iter().max().expect("four classes");
        let mut masses = [0u128; 4];
        for d in 0..4 {
            // r̂_d on 2^(−62) times 2^(w_d − w_max) on 2^(−62).
            masses[d] = ((unit(route[d], rt) * self.exponential.below_one(w[d] - top)) >> UNIT_BITS).max(1);
        }
        let total = masses.iter().sum();
        Ok(JoinedCell { masses, total, news })
    }

    /// The cell's actual class reaches the weight of its phase: its covector and curvature.
    pub fn receive(&mut self, cell: &JoinedCell, actual: usize, phase: usize) {
        // p̂_d on 2^(−30).
        let p: Vec<i128> = cell.masses.iter().map(|&m| (((m << 30) + cell.total / 2) / cell.total) as i128).collect();
        let mean: i128 = p.iter().zip(&cell.news).map(|(&p, &f)| p * f as i128).sum(); // 2^(−50)
        let second: i128 = p.iter().zip(&cell.news).map(|(&p, &f)| p * (f as i128) * (f as i128)).sum(); // 2^(−70)
        let mean20 = release(mean, 30);
        self.gradient[phase] += mean20 - cell.news[actual] as i128;
        let variance = release(second, 30) - mean20 * mean20; // 2^(−40)
        self.curvature[phase] += variance.max(0) * ln2_face() >> 30;
    }

    /// The section closes: each phase's weight takes its Newton step, and the covector reopens.
    pub fn step(&mut self) {
        for k in 0..4 {
            let g = self.gradient[k];
            self.gradient[k] = 0;
            if g == 0 {
                continue;
            }
            // Δα on 2^(−16) = G 2^(−20) / (ln 2 · H 2^(−40)) · 2^16 = G 2^36 / (ln 2 · H)
            //                = G 2^(36+30) / (ln2_face · H).
            let num = (g as i128) << 36;
            let den = (ln2_face() * self.curvature[k]) >> 30;
            let delta = if den > 0 { num / den } else { 0 };
            let delta = delta.clamp(-(2 * JOIN_REACH) as i128, (2 * JOIN_REACH) as i128) as i64;
            self.weights[k] = (self.weights[k] - delta).clamp(-JOIN_REACH, JOIN_REACH);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn keys(n: usize) -> Vec<u8> {
        // A fixed exterior key stream for the fixtures: the bytes of a counter's squares.
        (0..n as u64).flat_map(|i| (i.wrapping_mul(2654435761) ^ (i * i)).to_be_bytes()[4..].to_vec()).collect()
    }

    fn tiny() -> Tower {
        tiny_of(false)
    }

    /// The tiny tower, gated or not; a gated one's gate opens away from zero so its covector is read
    /// off the gate's midpoint.
    fn tiny_of(gated: bool) -> Tower {
        tiny_with(2, gated)
    }

    fn tiny_with(levels: usize, gated: bool) -> Tower {
        tiny_turning(levels, gated, false, false)
    }

    /// The tiny tower whose gated modes' turn may be keyed by the arriving symbol, and a turned
    /// one's pump; a turned one's turn, and a pumped one's depth and axis, open away from zero as
    /// its gate does.
    fn tiny_turning(levels: usize, gated: bool, turned: bool, pumped: bool) -> Tower {
        tiny_declared(levels, gated, turned, pumped, ContactLaw::Rectifying)
    }

    /// The tiny tower under any mode and contact law; a pair contact's second drive opens away from
    /// its one-sided opening (its material at the return's scale, its bias at unit) so its
    /// bilinear block carries a covector.
    fn tiny_declared(levels: usize, gated: bool, turned: bool, pumped: bool, contact: ContactLaw) -> Tower {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes: 2, contacts: 4, levels, gated, turned, pumped, contact };
        let mut tower = Tower::found(declaration, &keys(4096)).expect("founded");
        // Open the readout and the returns away from zero so every family carries a covector.
        let k = keys(8192);
        let mut i = 1000;
        let layout = tower.layout.clone();
        let mut fill = |theta: &mut Vec<i32>, start: usize, len: usize| {
            for v in &mut theta[start..start + len] {
                *v = (i32::from_be_bytes([k[4 * i], k[4 * i + 1], k[4 * i + 2], k[4 * i + 3]]) >> 8) / 4;
                i += 1;
            }
        };
        fill(&mut tower.theta, layout.readout, 16);
        for lv in &layout.levels {
            fill(&mut tower.theta, lv.ret, 16);
        }
        if gated {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.gate, 8);
                for v in &mut tower.theta[lv.gate..lv.gate + 8] {
                    *v *= 8;
                }
            }
        }
        if turned {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.turn, 8);
                for v in &mut tower.theta[lv.turn..lv.turn + 8] {
                    *v *= 8;
                }
            }
        }
        if contact != ContactLaw::Rectifying {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.pair, 16);
            }
        }
        if pumped {
            // The pump's depth at some tenths, its axis turned by a few half turns (measured: at
            // |κ| near ½ the quadrature is shed and the gate's covector falls below the reading;
            // the axis's covector scales with |β|).
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.pump, 8);
                fill(&mut tower.theta, lv.pump_axis, 8);
                for v in &mut tower.theta[lv.pump..lv.pump + 8] {
                    *v *= 4;
                }
                for v in &mut tower.theta[lv.pump_axis..lv.pump_axis + 8] {
                    *v *= 32;
                }
            }
        }
        tower
    }

    fn code(tower: &Tower, classes: &[usize]) -> i64 {
        let mut s = tower.rest();
        tower.read(&mut s, classes).expect("read")
    }

    /// The tension reading's `B = Σ dz f̄ᵀ`, `f̄ = (top, 1)`, is the readout's covector the reverse
    /// scan forms, and the reading moves the state as the forward does.
    #[test]
    fn the_tension_readings_bridge_is_the_readouts_covector() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let reaches = tower.reaches();
        let opening = tower.rest();
        let mut state = opening.clone();
        let cells = tower.forward(&mut state, &classes, &reaches).expect("forward");
        let g = tower.reverse(&opening, &cells, &classes, None).expect("reverse");
        let (a, w) = (tower.declaration.alphabet, tower.declaration.width);
        let (mut readout, mut bias, mut read) = (vec![0i128; a * w], vec![0i128; a], tower.rest());
        let mut count = 0;
        tower
            .read_tension(&mut read, &classes, |cell| {
                for c in 0..a {
                    bias[c] += cell.covector[c] as i128;
                    for j in 0..w {
                        readout[c * w + j] += cell.covector[c] as i128 * cell.top[j] as i128;
                    }
                }
                assert_eq!((cell.quadrature.len(), cell.below.len()), (w, w));
                count += 1;
                Ok(())
            })
            .expect("read");
        assert_eq!(count, classes.len() - 1);
        assert!(readout.iter().any(|&v| v != 0));
        assert_eq!(&g[tower.layout.readout..tower.layout.readout + a * w], &readout[..]);
        assert_eq!(&g[tower.layout.readout_bias..tower.layout.readout_bias + a], &bias[..]);
        assert_eq!(read, state);
    }

    /// The faces a joined face reads are the forward's: each cell's top is the tension reading's,
    /// its face is the one a step's advance returns, and the reading moves the state as they do.
    #[test]
    fn the_faces_read_beside_the_readout_are_the_forwards() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let mut tops = Vec::new();
        tower
            .read_tension(&mut tower.rest(), &classes, |cell| {
                tops.push(cell.top);
                Ok(())
            })
            .expect("tension");
        let (mut read, mut stepped) = (tower.rest(), tower.rest());
        let mut count = 0;
        tower
            .read_faces(&mut read, &classes, |i, top, face| {
                let (step_face, step_top) = tower.advance_top(&mut stepped, classes[i]).expect("advance");
                assert_eq!((top, face), (&step_top[..], &step_face));
                assert_eq!(top, &tops[i][..]);
                count += 1;
                Ok(())
            })
            .expect("read");
        assert_eq!(count, classes.len() - 1);
        assert_eq!(read, stepped);
    }

    #[test]
    fn text_restores_exactly() {
        text_restores_exactly_of(false);
        text_restores_exactly_of(true);
    }

    #[test]
    fn a_pumped_tower_restores_exactly() {
        let tower = tiny_turning(2, true, true, true);
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let turned = tiny_turning(2, true, true, false);
        assert_eq!(Tower::from_text(&turned.to_text()).expect("restored"), turned);
    }

    /// A pumped tower whose pump is at zero (`κ = 0`) codes every section exactly as its turned
    /// twin: the pump opens on the turn.
    #[test]
    fn a_pumped_tower_opens_on_its_turned_twin() {
        let turned = tiny_turning(2, true, true, false);
        let mut pumped = tiny_turning(2, true, true, true);
        for lv in pumped.layout.levels.clone() {
            pumped.theta[lv.pump..lv.pump + 8].fill(0);
            pumped.theta[lv.pump_bias..lv.pump_bias + 2].fill(0);
        }
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        assert_eq!(code(&pumped, &classes), code(&turned, &classes));
    }

    #[test]
    fn a_pair_tower_restores_exactly() {
        for contact in [ContactLaw::Pair, ContactLaw::PairLinear] {
            let tower = tiny_declared(2, true, true, true, contact);
            assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
            let plain = tiny_declared(2, false, false, false, contact);
            assert_eq!(Tower::from_text(&plain.to_text()).expect("restored"), plain);
        }
        assert!(Tower::from_text("moment-tower-v1 4 4 2 4 2 turned\n0\n").is_err());
        assert!(Tower::from_text("moment-tower-v1 4 4 2 4 2 pair gated\n0\n").is_err());
    }

    /// The bilinear block's weight on the memory rungs: none at founding (`W_b = 0`); with the
    /// second drive's material made the first's, symmetric; and with the read's material of every
    /// mode on the second rung at zero, none on that rung for either drive.
    #[test]
    fn the_bilinear_weight_sits_on_the_rungs_its_drives_read() {
        let declaration = |contact| TowerDeclaration { alphabet: 4, width: 4, modes: 16, contacts: 4, levels: 1, gated: false, turned: false, pumped: false, contact };
        assert!(Tower::found(declaration(ContactLaw::Rectifying), &keys(16384)).expect("founded").bilinear_rungs().is_err());
        let mut tower = Tower::found(declaration(ContactLaw::Pair), &keys(16384)).expect("founded");
        let zero = BigUint::from(0u32);
        let founded = tower.bilinear_rungs().expect("read");
        assert_eq!((founded.len(), founded[0].len()), (1, 2));
        assert!(founded[0].iter().flatten().all(|e| *e == zero));
        let lv = tower.layout.levels[0].clone();
        let (contact, pair) = (tower.theta[lv.contact..lv.contact + 16].to_vec(), lv.pair);
        tower.theta[pair..pair + 16].copy_from_slice(&contact);
        let e = &tower.bilinear_rungs().expect("read")[0];
        assert_eq!(e[0][1], e[1][0]);
        assert!(e.iter().flatten().all(|x| *x > zero));
        for i in 0..4 {
            for k in 8..16 {
                tower.theta[lv.read_re + i * 16 + k] = 0;
                tower.theta[lv.read_im + i * 16 + k] = 0;
            }
        }
        let e = &tower.bilinear_rungs().expect("read")[0];
        assert!(e[0][0] > zero);
        assert_eq!([&e[0][1], &e[1][0], &e[1][1]], [&zero, &zero, &zero]);
    }

    /// Founded, the pair contact's second drive is `W_b = 0`, `b_b = 1`: the pair contact and its
    /// linear foil code every passage alike, the one-sided contact `v = W_a r̂ + b_a`.
    #[test]
    fn the_pair_contact_and_its_foil_open_together() {
        let declaration = |contact| TowerDeclaration { alphabet: 4, width: 4, modes: 2, contacts: 4, levels: 2, gated: true, turned: true, pumped: true, contact };
        let mut pair = Tower::found(declaration(ContactLaw::Pair), &keys(4096)).expect("founded");
        let mut foil = Tower::found(declaration(ContactLaw::PairLinear), &keys(4096)).expect("founded");
        // Open the returns and the readout away from zero, the same in both.
        for lv in pair.layout.levels.clone() {
            for (i, v) in pair.theta[lv.ret..lv.ret + 16].iter_mut().enumerate() {
                *v = (i as i32 - 8) << 20;
            }
        }
        let ro = pair.layout.readout;
        for (i, v) in pair.theta[ro..ro + 16].iter_mut().enumerate() {
            *v = (7 - i as i32) << 21;
        }
        foil.theta.clone_from(&pair.theta);
        assert_eq!(code(&pair, &PASSAGE), code(&foil, &PASSAGE));
        // Once the second drive's material moves, the product's block separates them.
        let lv = pair.layout.levels[0];
        for (i, v) in pair.theta[lv.pair..lv.pair + 16].iter_mut().enumerate() {
            *v = (i as i32 - 5) << 22;
        }
        foil.theta.clone_from(&pair.theta);
        assert_ne!(code(&pair, &PASSAGE), code(&foil, &PASSAGE));
    }

    #[test]
    fn the_pair_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_declared(2, false, false, false, ContactLaw::Pair), false, &PASSAGE, 10);
        the_covector_of_tower_matches_the_code_difference(tiny_declared(2, true, false, false, ContactLaw::Pair), true, &PASSAGE, 10);
    }

    #[test]
    fn the_linear_foils_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_declared(2, false, false, false, ContactLaw::PairLinear), false, &PASSAGE, 10);
    }

    fn text_restores_exactly_of(gated: bool) {
        let tower = tiny_of(gated);
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let mut learner = TowerLearner::new(tower, 6);
        let seq: Vec<usize> = (0..17).map(|i| i % 4).collect();
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let restored = TowerLearner::from_text(&learner.to_text()).expect("restored");
        assert_eq!(restored.tower, learner.tower);
        assert_eq!(restored.to_text(), learner.to_text());
    }

    #[test]
    fn the_covector_matches_the_code_difference() {
        the_covector_matches_the_code_difference_of(false);
    }

    #[test]
    fn the_gated_covector_matches_the_code_difference() {
        the_covector_matches_the_code_difference_of(true);
    }

    /// The thirteen classes every fixture reads.
    const PASSAGE: [usize; 13] = [0, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];

    #[test]
    fn the_turned_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_turning(2, true, true, false), true, &PASSAGE, 10);
    }

    /// Read over 37 classes: on thirteen the pump axis's covector (it scales with |β|) stays below
    /// the reading's 1/64 bit a unit (measured), and the longer passage carries it. Its steps are
    /// `2^(−9)` units (measured): at `2^(−10)` the faces' release moved the second level's turn's
    /// fitted slope to −112 against a covector of −91 (×2^20), at `2^(−8)` it read −93, but steps
    /// that wide moved contacts across their kinks and left 29 of 39 families read.
    #[test]
    fn the_pumped_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tiny_turning(2, true, true, true), true, &classes, 9);
    }

    fn the_covector_matches_the_code_difference_of(gated: bool) {
        the_covector_of_tower_matches_the_code_difference(tiny_of(gated), gated, &PASSAGE, 10);
    }

    fn the_covector_of_tower_matches_the_code_difference(tower: Tower, gated: bool, classes: &[usize], step: u32) {
        the_covector_of_tower_matches_the_code_difference_compared(tower, gated, classes, None, step);
    }

    /// The code of a passage whose faces are compared with `compared` (the classes read when it is
    /// `None`), read from rest.
    fn compared_code(tower: &Tower, classes: &[usize], compared: Option<&[Option<usize>]>) -> i64 {
        let Some(compared) = compared else { return code(tower, classes) };
        let mut s = tower.rest();
        let cells = tower.forward(&mut s, classes, &tower.reaches()).expect("forward");
        cells.iter().enumerate().filter_map(|(i, cell)| compared[i + 1].map(|t| cell.face.code(t))).sum()
    }

    /// The code read at sixteen steps `k 2^(−step)` units, `0 < |k| ≤ 8`.
    fn the_covector_of_tower_matches_the_code_difference_compared(
        tower: Tower,
        gated: bool,
        classes: &[usize],
        compared: Option<&[Option<usize>]>,
        step: u32,
    ) {
        let opening = tower.rest();
        let reaches = tower.reaches();
        let mut s = opening.clone();
        let cells = tower.forward(&mut s, &classes, &reaches).expect("forward");
        let mut g = tower.reverse(&opening, &cells, &classes, compared).expect("reverse");
        tower.to_step_grain(&mut g);
        // Which contacts conduct at every cell, and each pump's depth's sign: the covector is the
        // derivative on the passage's own side of every kink, so a perturbation that moves a contact
        // or a pump's |κ| across its kink is not read.
        let conducting = |t: &Tower| -> Vec<bool> {
            let mut s = t.rest();
            let cells = t.forward(&mut s, &classes, &t.reaches()).expect("forward");
            cells
                .iter()
                .flat_map(|c| c.levels.iter().flat_map(|l| l.drive.iter().filter(|_| l.pair.is_empty()).map(|&a| a > 0).chain(l.gate.iter().map(|m| m.kappa > 0))).collect::<Vec<_>>())
                .collect()
        };
        let base = conducting(&tower);
        // Every family: its parameters by covector, largest first, the first whose steps of up to
        // ±2^(−7) units keep every contact on its side. The code is read at sixteen steps `k h`,
        // `h = 2^(−10)` units, `0 < |k| ≤ 8`, and its slope fitted, `Σ k ΔL / (h Σ k²)`: the forward
        // releases every face to `2^(−16)`, and on the tiny tower that rounding moves one central
        // difference by up to a seventh (measured on the gated tower: ±2^(−7), ±2^(−8) and ±2^(−9)
        // units read 92.0, 105.4 and 91.2 against a covector of 104.6, ×10⁶).
        let (mut checked, mut gates_checked, mut turns_checked, mut pumps_checked, mut pairs_checked) = (0, 0, 0, 0, 0);
        let base_code = compared_code(&tower, &classes, compared);
        for &(start, len, grain) in &tower.layout.families {
            let mut order: Vec<usize> = (start..start + len).collect();
            order.sort_by_key(|&i| std::cmp::Reverse(g[i].abs()));
            'parameter: for i in order {
                let gi = g[i];
                if gi.abs() < 1i128 << (STEP_BITS - 6) {
                    break; // below 1/64 bit a unit the difference over ±2^(−7) units nears the reading's grain
                }
                let h = 1i32 << (grain - step);
                let (mut moment, mut spread) = (0i128, 0i128);
                for k in (-8i32..=8).filter(|&k| k != 0) {
                    let mut moved = tower.clone();
                    moved.theta[i] += k * h;
                    if conducting(&moved) != base {
                        continue 'parameter;
                    }
                    moment += k as i128 * (compared_code(&moved, &classes, compared) - base_code) as i128; // on 2^(−20)
                    spread += (k * k) as i128;
                }
                // The fitted slope against g, both in bits a unit on 2^(−32).
                let numeric = (moment << (STEP_BITS - READ_BITS)) * (1i128 << grain) / (h as i128 * spread);
                let error = (numeric - gi).abs();
                assert!(error * 10 <= gi.abs(), "family at {start} grain {grain}, parameter {i}: covector {gi} against {numeric}");
                checked += 1;
                gates_checked += tower.layout.levels.iter().any(|lv| gated && (start == lv.gate || start == lv.gate_bias)) as usize;
                turns_checked += tower.layout.levels.iter().any(|lv| tower.declaration.turned && (start == lv.turn || start == lv.turn_bias)) as usize;
                pumps_checked += tower.layout.levels.iter().any(|lv| tower.declaration.pumped && [lv.pump, lv.pump_bias, lv.pump_axis, lv.pump_axis_bias].contains(&start)) as usize;
                pairs_checked += tower.layout.levels.iter().any(|lv| tower.declaration.contact != ContactLaw::Rectifying && (start == lv.pair || start == lv.pair_bias)) as usize;
                break;
            }
        }
        // A gated tower's gate material and bias are read at the first level (the second level's
        // gate covectors fall below 1/64 bit a unit on this fixture).
        assert!(!gated || gates_checked >= 2, "only {gates_checked} gate families carried a readable covector");
        assert!(!tower.declaration.turned || turns_checked >= 2, "only {turns_checked} turn families carried a readable covector");
        assert!(!tower.declaration.pumped || pumps_checked >= 4, "only {pumps_checked} pump families carried a readable covector");
        assert!(tower.declaration.contact == ContactLaw::Rectifying || pairs_checked >= 2, "only {pairs_checked} pair families carried a readable covector");
        assert!(checked * 4 >= tower.layout.families.len() * 3, "only {checked} families carried a readable covector");
    }

    #[test]
    fn the_opening_credit_completes_the_passage_covector() {
        the_opening_credit_completes_the_passage_covector_of(false);
        the_opening_credit_completes_the_passage_covector_of(true);
    }

    /// On one level every carried path is the level's own recurrence, so a passage's covector read
    /// as one section equals its two halves' with the second opening on the first's credit, in
    /// every recurrence family, to the moments' release; without the credit the halves miss what
    /// the second opening carries.
    fn the_opening_credit_completes_the_passage_covector_of(gated: bool) {
        let tower = tiny_with(1, gated);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0, 2, 2, 1, 3, 0, 1, 1, 2, 3, 0, 0, 1];
        let half = classes.len() / 2;
        let reaches = tower.reaches();
        let covector = |opening: &TowerState, part: &[usize]| -> (Vec<i128>, TowerState) {
            let mut s = opening.clone();
            let cells = tower.forward(&mut s, part, &reaches).expect("forward");
            let g = tower.reverse(opening, &cells, part, None).expect("reverse");
            if let Some(credit) = s.credit.as_mut() {
                tower.advance_credit(credit, opening, &cells, &reaches).expect("credit");
            }
            (g, s)
        };
        let rest = tower.rest_with_credit();
        let (whole, _) = covector(&rest, &classes);
        let (first, carried) = covector(&rest, &classes[..=half]);
        let (second, _) = covector(&carried, &classes[half..]);
        let bare = TowerState { credit: None, ..carried.clone() };
        let (second_bare, _) = covector(&bare, &classes[half..]);
        let lv = tower.layout.levels[0];
        let d = &tower.declaration;
        let mut families = vec![(lv.move_re, d.modes), (lv.move_im, d.modes), (lv.push_re, d.modes * d.width), (lv.push_im, d.modes * d.width)];
        if gated {
            families.extend([(lv.gate, d.modes * d.width), (lv.gate_bias, d.modes)]);
        }
        let (mut credited, mut missed, mut scale) = (0i128, 0i128, 0i128);
        for (start, len) in families {
            for i in start..start + len {
                let error = (whole[i] - first[i] - second[i]).abs();
                // Each moment releases one grain a cell; the parameters' covectors carry tens of
                // thousands of grains on this fixture.
                assert!(error * 64 <= whole[i].abs().max(1 << 12), "family at {start}, parameter {i}: whole {} against halves {}", whole[i], first[i] + second[i]);
                credited += error;
                missed += (whole[i] - first[i] - second_bare[i]).abs();
                scale += whole[i].abs();
            }
        }
        assert!(missed >= 16 * credited.max(1) && missed * 64 >= scale, "the credit carried {credited} of error against {missed} without it, over {scale}");
    }

    #[test]
    fn the_move_chart_covector_matches_its_step() {
        the_move_chart_covector_matches_its_step_of(false);
    }

    #[test]
    fn the_gated_move_chart_covector_matches_its_step() {
        the_move_chart_covector_matches_its_step_of(true);
    }

    fn the_move_chart_covector_matches_its_step_of(gated: bool) {
        let tower = tiny_of(gated);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let opening = tower.rest();
        let reaches = tower.reaches();
        let mut s = opening.clone();
        let cells = tower.forward(&mut s, &classes, &reaches).expect("forward");
        let mut g = tower.reverse(&opening, &cells, &classes, None).expect("reverse");
        tower.to_step_grain(&mut g);
        tower.to_move_chart(&mut g);
        // Each chart coordinate of each level: the mode with the largest covector, stepped by ±2^(−7).
        let mut checked = 0;
        for lv in &tower.layout.levels {
            for slot in [lv.move_re, lv.move_im] {
                let (i, gi) = (slot..slot + tower.declaration.modes).map(|i| (i, g[i])).max_by_key(|(_, v)| v.abs()).expect("modes");
                if gi.abs() < 1i128 << (STEP_BITS - 6) {
                    continue;
                }
                let h = 1i128 << (MOVE_BITS - 7);
                let mut step = vec![0i128; g.len()];
                step[i] = h;
                let mut minus = tower.clone();
                minus.move_by_chart(&step, 0).expect("chart step");
                step[i] = -h;
                let mut plus = tower.clone();
                plus.move_by_chart(&step, 0).expect("chart step");
                let diff = (code(&plus, &classes) - code(&minus, &classes)) as i128;
                let numeric = (diff << (STEP_BITS - READ_BITS)) * (1i128 << MOVE_BITS) / (2 * h);
                assert!((numeric - gi).abs() * 10 <= gi.abs(), "chart coordinate at {i}: covector {gi} against {numeric}");
                checked += 1;
            }
        }
        assert!(checked >= 2, "only {checked} chart coordinates carried a readable covector");
    }

    #[test]
    fn the_cell_faces_split_the_byte_face_exactly() {
        let masses: Vec<u128> = (0..256u128).map(|b| 1 + (b * b) % 97).collect();
        let total = masses.iter().sum();
        let face = TowerFace { masses: masses.clone(), total };
        // The first cell's masses sum to the face's total; each later phase splits its prefix's mass.
        assert_eq!(face.cell_masses(0, 0).expect("cell").iter().sum::<u128>(), total);
        for byte in [0usize, 77, 200, 255] {
            let mut prefix = 0;
            let mut mass = total;
            for phase in 0..4 {
                let cells = face.cell_masses(prefix, phase).expect("cell");
                assert_eq!(cells.iter().sum::<u128>(), mass);
                let d = (byte >> (6 - 2 * phase)) & 3;
                mass = cells[d];
                prefix = (prefix << 2) | d;
            }
            assert_eq!(mass, masses[byte]);
        }
        assert!(face.cell_masses(4, 1).is_err());
        assert!(face.cell_masses(0, 4).is_err());
    }

    #[test]
    fn the_cell_chart_covers_any_alphabet_and_cells_past_it_hold_nothing() {
        assert_eq!([2, 4, 5, 16, 17, 256, 1318].map(cell_phases), [1, 1, 2, 2, 3, 4, 6]);
        // Five classes take two cells: the first splits 1+2+3+4 from the fifth, past which no
        // class stands.
        let masses = vec![1u128, 2, 3, 4, 5];
        let face = TowerFace { masses, total: 15 };
        assert_eq!(face.cell_masses(0, 0).expect("cell"), [10, 5, 0, 0]);
        assert_eq!(face.cell_masses(0, 1).expect("cell"), [1, 2, 3, 4]);
        assert_eq!(face.cell_masses(1, 1).expect("cell"), [5, 0, 0, 0]);
        assert_eq!(face.cell_masses(2, 1).expect("cell"), [0, 0, 0, 0]);
        assert!(face.cell_masses(0, 2).is_err());
    }

    #[test]
    fn the_join_reads_the_route_at_zero_and_moves_toward_the_face_that_codes_less() {
        let route = [400u128, 300, 200, 100];
        let tower = [10u128, 10, 10, 970];
        let at_zero = CellJoin::new([0; 4]).face(&route, &tower, 0).expect("joined");
        for d in 0..4 {
            // r̂ on 2^(−62) timed by 2^0: the route's own face.
            assert_eq!(at_zero.masses[d], unit_of(route[d], 1000), "{at_zero:?}");
        }
        // The class the tower favours keeps arriving: the weight of its phase grows past ½.
        let mut join = CellJoin::default();
        for _ in 0..8 {
            for _ in 0..64 {
                let cell = join.face(&route, &tower, 2).expect("joined");
                join.receive(&cell, 3, 2);
            }
            join.step();
        }
        assert!(join.weights[2] > 1 << (JOIN_BITS - 1), "{:?}", join.weights);
        assert_eq!(join.weights[0], 1 << (JOIN_BITS - 1));
        let cell = join.face(&route, &tower, 2).expect("joined");
        assert!(cell.code(3) < code_of(route[3], 1000));
    }

    #[test]
    fn a_gate_at_its_midpoint_reads_the_ungated_tower() {
        let plain = tiny();
        // The same material with each level's gate at zero.
        let mut gated = tiny_of(true);
        for lv in gated.layout.levels.clone() {
            gated.theta[lv.gate..lv.gate + 8].fill(0);
        }
        let ungated: Vec<i32> = gated
            .layout
            .families
            .iter()
            .filter(|&&(start, _, _)| !gated.layout.levels.iter().any(|lv| start == lv.gate || start == lv.gate_bias))
            .flat_map(|&(start, len, _)| gated.theta[start..start + len].to_vec())
            .collect();
        assert_eq!(ungated, plain.theta);
        let classes: Vec<usize> = (0..200).map(|i| (i * i + 3 * i) % 4).collect();
        let (a, b) = (code(&plain, &classes), code(&gated, &classes));
        // r = ½ reproduces each modulus to the grain of log₂ and 2^x: the codes agree to a
        // thousandth of a bit over the passage.
        assert!((a - b).abs() * 1000 < 1i64 << READ_BITS, "{a} against {b}");
        assert_ne!(gated.reaches().gates.len(), 0);
    }

    #[test]
    fn a_silent_moment_reaches_zero() {
        // The stalled moments of a contact that stopped conducting: the covector is zero from here on.
        let (mut m, mut v) = (3i128, 127i128);
        for _ in 0..200 {
            m = toward(m, 0, FIRST_RATE);
            v = toward(v, 0, SECOND_RATE);
        }
        assert_eq!((m, v), (0, 0));
        // Released to the nearest grain alone, they would stay.
        assert_eq!(3 + release(-3, FIRST_RATE), 3);
        assert_eq!(127 + release(-127, SECOND_RATE), 127);
        // A moment far from its input moves by the rounded release, as before.
        assert_eq!(toward(1000, 0, FIRST_RATE), 1000 + release(-1000, FIRST_RATE));
    }

    #[test]
    fn a_section_learns_a_repeating_passage() {
        a_section_learns_a_repeating_passage_of(false);
        a_section_learns_a_repeating_passage_of(true);
    }

    fn a_section_learns_a_repeating_passage_of(gated: bool) {
        let declaration = TowerDeclaration { alphabet: 4, width: 8, modes: 4, contacts: 8, levels: 1, gated, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let tower = Tower::found(declaration, &keys(4096)).expect("founded");
        let mut learner = TowerLearner::new(tower, 5);
        let passage: Vec<usize> = (0..4096).map(|i| [0, 1, 2, 1, 3][i % 5]).collect();
        let mut states = vec![learner.tower.rest(), learner.tower.rest()];
        let mut last = SectionReceipt { cells: 0, code_before: 0, code_after: 0, halvings: 0, deposited: false, parts: Vec::new() };
        for section in 0..60 {
            let a = &passage[section * 32..section * 32 + 33];
            let b = &passage[2048 + section * 32..2048 + section * 32 + 33];
            last = learner.section(&mut states, &[a, b]).expect("section");
            // The certificate compares the exact products; the reading releases each cell to
            // 2^(−20) bits, so a certified step below that grain can read as a tie.
            assert!(!last.deposited || last.code_after <= last.code_before + last.cells as i64, "section {section}: {last:?}");
            // The parts' codes are the section's, split by part.
            assert_eq!(last.parts.len(), 2);
            assert_eq!(last.parts.iter().map(|p| p.0).sum::<i64>(), last.code_before, "section {section}");
            assert_eq!(last.parts.iter().map(|p| p.1).sum::<i64>(), last.code_after, "section {section}");
            assert!(last.deposited || last.parts.iter().all(|p| p.0 == p.1), "section {section}");
        }
        // Under a quarter of a bit a class (the flat face codes two bits).
        assert!(last.code_after * 4 < (last.cells as i64) << READ_BITS, "{last:?}");
    }

    /// A place compared with nothing is the tower's own release re-entering what it reads.
    /// Compared everywhere with the class that arrived, a section is the plain section; compared
    /// nowhere, a passage sends no covector and codes nothing; and the covectors of two
    /// complementary comparisons sum to the plain covector up to the reverse scan's releases.
    #[test]
    fn an_uncompared_class_sends_no_covector_and_is_not_counted() {
        let tower = tiny_turning(2, true, true, true);
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        let opening = tower.rest();
        let mut s = opening.clone();
        let cells = tower.forward(&mut s, &classes, &tower.reaches()).expect("forward");
        let plain = tower.reverse(&opening, &cells, &classes, None).expect("reverse");
        let all: Vec<Option<usize>> = classes.iter().map(|&c| Some(c)).collect();
        assert_eq!(tower.reverse(&opening, &cells, &classes, Some(&all)).expect("reverse"), plain);
        let none = vec![None; classes.len()];
        assert!(tower.reverse(&opening, &cells, &classes, Some(&none)).expect("reverse").iter().all(|&v| v == 0));
        // Every third class re-entering, and its complement.
        let some: Vec<Option<usize>> = classes.iter().enumerate().map(|(i, &c)| (i % 3 != 1).then_some(c)).collect();
        let rest: Vec<Option<usize>> = classes.iter().enumerate().map(|(i, &c)| (i % 3 == 1).then_some(c)).collect();
        let a = tower.reverse(&opening, &cells, &classes, Some(&some)).expect("reverse");
        let b = tower.reverse(&opening, &cells, &classes, Some(&rest)).expect("reverse");
        assert!(a != plain && b.iter().any(|&v| v != 0));
        let (gap, size): (i128, i128) = a.iter().zip(&b).zip(&plain).fold((0, 0), |(g, n), ((x, y), p)| (g + (x + y - p).abs(), n + p.abs()));
        assert!(gap * 1000 <= size, "complementary comparisons sum to {gap} away from a covector of {size}");
        // The sections: compared everywhere as the plain one, compared nowhere coding nothing.
        let mut plain_learner = TowerLearner::new(tower.clone(), 5);
        let mut compared_learner = TowerLearner::new(tower.clone(), 5);
        let (mut s1, mut s2) = (vec![tower.rest()], vec![tower.rest()]);
        let r1 = plain_learner.section(&mut s1, &[&classes]).expect("section");
        let r2 = compared_learner.section_compared(&mut s2, &[&classes], Some(&[&all])).expect("section");
        assert_eq!((r1.code_before, r1.code_after, r1.deposited, r1.cells), (r2.code_before, r2.code_after, r2.deposited, r2.cells));
        assert_eq!(plain_learner.tower, compared_learner.tower);
        assert_eq!(s1, s2);
        let mut silent = TowerLearner::new(tower.clone(), 5);
        let r = silent.section_compared(&mut vec![tower.rest()], &[&classes], Some(&[&none])).expect("section");
        assert_eq!((r.cells, r.code_before, r.deposited), (0, 0, false));
        assert_eq!(silent.tower, tower);
    }

    /// The tower's own release read against another class where the two part: the passage reads
    /// the release while the faces are compared with the truth (every fifth place another class,
    /// every seventh compared with nothing), and the covector is still the slope of that
    /// comparison's code, read on the gated tower: on the pumped one only 26 to 28 of its 39
    /// families carried a readable covector over 37 or 61 classes (measured), every one read
    /// matching.
    #[test]
    fn the_compared_covector_matches_the_code_difference() {
        let compared: Vec<Option<usize>> =
            PASSAGE.iter().enumerate().map(|(i, &c)| if i % 7 == 3 { None } else if i % 5 == 2 { Some((c + 1) % 4) } else { Some(c) }).collect();
        the_covector_of_tower_matches_the_code_difference_compared(tiny_of(true), true, &PASSAGE, Some(&compared), 10);
    }
}
