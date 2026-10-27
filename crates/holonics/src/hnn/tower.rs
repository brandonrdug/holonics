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
use crate::hnn::keyed_modes::{dyadic_turn, ln2_face, log2_face, release, Exponential};
use num_bigint::BigUint;
use rayon::prelude::*;

pub mod duplex;
pub mod realization;

use realization::{HostPass, PassRealization, Slot};

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
pub const FIRST_RATE: u32 = 3;
pub const SECOND_RATE: u32 = 8;
const UNIT_BITS: u32 = 62;

/// Refusals of the tower's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TowerError {
    #[error("tower refused: {0}")]
    Refused(&'static str),
    /// A declared realization of the section's pass refused (`realization`), with its reason.
    #[error("tower realization refused: {0}")]
    Realization(String),
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

/// [definition; agent-inferred, October 25] **A founding's turn ladder**: the turns a level's
/// modes are founded on, rung by rung (rung `s` the modes of memory `|λ| = 1 − 2^(−s)`, `J` modes a
/// rung).
///
/// A mode that turns by `θ` a class puts each class at a phase set by its place in the passage, so
/// a mode that turns many times over its memory holds the order of what it heard and scatters a
/// long source by its length, and a mode that turns less than once holds its content. Measured on
/// the digits' images (52 to 298 classes; the record
/// `2026-10-25_ONE_LISTENER_HEARS_GSM8K_MNIST_AND_SPEECH_AS_SECTIONS_OF_ONE_PASSAGE.md`, "Why the
/// state forgets the image"): founded fixed, the four slowest rungs at the label named 87 to 94 of
/// 500 held-out labels, founded scaled 146 to 148, and the scaled tower named 55 against 46 after
/// one pass; but a text tower alone coded GSM8K answers at 2.760 bits a class against 2.730 and a
/// speech tower its half-cycles at 3.006 against 2.907, the slow resonators the fixed ladder holds.
/// The whole listener founded on both ladders at 128 modes, after one pass, coded every mark but
/// the half-cycles below the fixed ladder at 128 (transcripts 6.059 bits a class against 6.576,
/// labels 4.226 against 4.397, answers 2.774 against 2.795; half-cycles 3.620 against 3.564).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TurnLadder {
    /// `j·π/J` on every rung: each rung resonates at the same `J` turns, a slow mode as a narrow
    /// resonator at a fixed period.
    Fixed,
    /// `j·π/(J·2^(s−1))` on rung `s`, `s` held at the margin's rung: each mode turns less than
    /// once over its memory `2^s`.
    Scaled,
    /// Both, half the bank each over the same rungs: modes `0..N/2` fixed and `N/2..N` scaled.
    Both,
}

/// [definition; agent-inferred, October 24] **The resident pair face**: `k` founded bilinear forms
/// read at the pair `p` of the class before and the class arriving,
///
/// ```text
/// c_v(p) = x̂_curᵀ W_v ŷ_prev,    x̂ = (E₀(cur), 1),  ŷ = (E₀(prev), 1),  ŷ_start = (0, 1)
/// ```
///
/// on `2^(−16)` (the unit coordinate at `2^16`), each form's exact values released by its founding
/// shift (rounded half up), so that on the founding text's pairs they lie below `2^16`. `E₀` is the
/// encoding the forms were founded on and is held with them: the face is the forms' face at their
/// founding, generated from `W_v` and `E₀` whenever the tower is read back (a navigator's resident
/// face, never a stored table of answers). The forms come from the tension a frozen tower leaves
/// (the record `2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT…`, "The block of pair forms"): they are
/// held fixed, and a new founding is how they change, because reading them per cell from the moving
/// encoding costs `k (d + 1)²` products a cell (about `2.4·10^11` a pass of the Holonics text).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairFace {
    alphabet: usize,
    /// Each form's `W_v`, `(d + 1)²` integers, the current class's coordinate by the class before's.
    forms: Vec<Vec<i64>>,
    shifts: Vec<i32>,
    /// `E₀`, `A × d` on `2^(−16)`.
    opening: Vec<i32>,
    /// `c_v(prev, cur)` at `((prev · A + cur) · k + v)`, `prev` over the alphabet and the start `A`.
    values: Vec<i32>,
}

impl PairFace {
    /// The face of `forms` founded on the encoding `opening` (`A × d`), each form's values released
    /// by its shift. Refused when a value outgrows its 32-bit carrier.
    pub fn new(alphabet: usize, width: usize, opening: Vec<i32>, forms: Vec<Vec<i64>>, shifts: Vec<i32>) -> Result<Self> {
        let hat = width + 1;
        if alphabet < 2 || opening.len() != alphabet * width || forms.is_empty() || forms.len() != shifts.len() || forms.iter().any(|w| w.len() != hat * hat) {
            return refuse("a pair face needs one shift and a (d + 1)² weight a form over the founding encoding");
        }
        let k = forms.len();
        let wide: Vec<Vec<i128>> = forms.iter().map(|w| Self::exact_values(alphabet, width, &opening, w)).collect();
        let mut values = vec![0i32; (alphabet + 1) * alphabet * k];
        for (v, (exact, &shift)) in wide.iter().zip(&shifts).enumerate() {
            for (pair, &x) in exact.iter().enumerate() {
                values[pair * k + v] = fit32(shifted(x, shift)?, "a pair form's value outgrew its 32-bit carrier")?;
            }
        }
        Ok(Self { alphabet, forms, shifts, opening, values })
    }

    /// A form's exact values `x̂ᵀ W ŷ` at every pair, `(prev · A + cur)`, on `2^(−32)` the form's grain.
    pub fn exact_values(alphabet: usize, width: usize, opening: &[i32], w: &[i64]) -> Vec<i128> {
        let hat = width + 1;
        let face = |u: usize| -> Vec<i128> {
            let mut x: Vec<i128> = if u < alphabet { opening[u * width..(u + 1) * width].iter().map(|&e| e as i128).collect() } else { vec![0; width] };
            x.push(1 << FACE_BITS);
            x
        };
        let cur: Vec<Vec<i128>> = (0..alphabet).map(face).collect();
        (0..=alphabet)
            .into_par_iter()
            .flat_map_iter(|prev| {
                let y = face(prev);
                let u: Vec<i128> = (0..hat).map(|i| w[i * hat..(i + 1) * hat].iter().zip(&y).map(|(&a, &b)| a as i128 * b).sum()).collect();
                cur.iter().map(move |x| x.iter().zip(&u).map(|(&a, &b)| a * b).sum::<i128>()).collect::<Vec<_>>()
            })
            .collect()
    }

    /// The count of forms `k`.
    pub fn forms(&self) -> usize {
        self.forms.len()
    }

    /// The face at a pair, `c(prev, cur)`, `prev` the start at `A`.
    pub fn at(&self, prev: usize, cur: usize) -> &[i32] {
        let k = self.forms.len();
        let row = (prev * self.alphabet + cur) * k;
        &self.values[row..row + k]
    }

    fn to_text(&self) -> String {
        let join = |xs: &mut dyn Iterator<Item = String>| xs.collect::<Vec<_>>().join(" ");
        format!(
            "pair-face {} {}\n{}\n{}\n",
            self.forms.len(),
            join(&mut self.shifts.iter().map(|s| s.to_string())),
            join(&mut self.forms.iter().flatten().map(|v| v.to_string())),
            join(&mut self.opening.iter().map(|v| v.to_string()))
        )
    }

    fn from_text(head: &str, forms: &str, opening: &str, alphabet: usize, width: usize) -> Result<Self> {
        let bad = TowerError::Refused("not a pair face's text");
        let words: Vec<&str> = head.split(' ').collect();
        if words.len() < 3 || words[0] != "pair-face" {
            return Err(bad);
        }
        let k: usize = words[1].parse().map_err(|_| bad.clone())?;
        let shifts: Vec<i32> = words[2..].iter().map(|s| s.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
        let flat: Vec<i64> = forms.split(' ').map(|s| s.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
        let opening: Vec<i32> = opening.split(' ').map(|s| s.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
        let hat = width + 1;
        if shifts.len() != k || flat.len() != k * hat * hat {
            return Err(bad);
        }
        Self::new(alphabet, width, opening, flat.chunks(hat * hat).map(|w| w.to_vec()).collect(), shifts)
    }
}

/// [definition; agent-inferred, October 25] **A founded ring rank** (the example's
/// `found-tower-ring`, record `2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT…`, "The machine founds
/// the units' ring at a received landmark"): a situated form pushed into a ring that rides one
/// placement mode's own moves,
///
/// ```text
/// v_t = (aᵀŝ_t)(bᵀx̂_t)(gᵀ(ŝ_t, 2^16)),   r_t = λ_(m,t) r_(t−1) + β_(m,t) r̄_(t−1) + v_t
/// ```
///
/// with `ŝ` one level's carried face before the move ([`carried_face`]'s order, each mode's
/// `(re, im)` on `2^(−16)`), `x̂ = (E(u), 2^16)` the arriving class, `a` and `b` complex (`[re, im]`)
/// and `g` real. Each factor's value is released by its own `release` (below `2^40` at its
/// founding bound), the push by `push_shift`, and the ring's read by `read_shift`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingRank {
    pub a: [Vec<i64>; 2],
    pub b: [Vec<i64>; 2],
    pub g: Vec<i64>,
    pub release: [u32; 3],
    pub push_shift: u32,
    pub read_shift: u32,
}

fn dot64(a: &[i64], x: &[i64]) -> i128 {
    a.iter().zip(x).map(|(&p, &q)| p as i128 * q as i128).sum()
}

impl RingRank {
    /// The state's factors at a carried face `ŝ`: `α = aᵀŝ` and `γ = gᵀ(ŝ, 2^16)`, each released.
    pub fn state_factors(&self, s: &[i64]) -> ((i128, i128), i128) {
        let [ra, _, rg] = self.release;
        let dims = s.len();
        let alpha = (release(dot64(&self.a[0], s), ra), release(dot64(&self.a[1], s), ra));
        let gamma = release(dot64(&self.g[..dims], s) + self.g[dims] as i128 * (1 << FACE_BITS), rg);
        (alpha, gamma)
    }

    /// The pool's value at an arriving class's `x̂`: `β = bᵀx̂`, released.
    pub fn pool(&self, hat: &[i64]) -> (i128, i128) {
        let rb = self.release[1];
        (release(dot64(&self.b[0], hat), rb), release(dot64(&self.b[1], hat), rb))
    }

    /// The push `v = αβγ` released by `push_shift`. Three factors released below `2^40` multiply
    /// below `2^121`; a reading past its founding bound that leaves 128 bits is refused.
    pub fn push(&self, alpha: (i128, i128), beta: (i128, i128), gamma: i128) -> Result<(i128, i128)> {
        let wide = TowerError::Refused("a ring's push outgrew its 128-bit carrier");
        let mul = |x: i128, y: i128| x.checked_mul(y).ok_or(wide.clone());
        let re = mul(alpha.0, beta.0)?.checked_sub(mul(alpha.1, beta.1)?).ok_or(wide.clone())?;
        let im = mul(alpha.0, beta.1)?.checked_add(mul(alpha.1, beta.0)?).ok_or(wide.clone())?;
        Ok((release(mul(re, gamma)?, self.push_shift), release(mul(im, gamma)?, self.push_shift)))
    }
}

/// [agent-inferred, October 25] **A ring factor on the material's grain**: the factor's parts
/// (`a`'s or `b`'s two, or `g`) scaled together by `2^k` so their root mean square lies in
/// `[2^24, 2^25)`, the material's unit, and its release moved by the same `k`. A factor's scale is
/// a gauge (each rank is read as a ratio to its own power, [`RingFace`]), so the material's step,
/// which moves an entry by about `2^(−rate)` units, moves a factor by that share of its own power
/// whatever scale it was founded at. Exact where `k ≥ 0`; a factor founded wider than the material
/// keeps 24 bits of its power. Refused when the release would fall below zero or an entry leave 32
/// bits.
fn factor_on_material(parts: &[&[i64]], release_bits: u32) -> Result<(Vec<i32>, u32)> {
    let squares: num_bigint::BigUint = parts.iter().flat_map(|p| p.iter()).map(|&v| num_bigint::BigUint::from(v.unsigned_abs()).pow(2)).sum();
    let count = parts.iter().map(|p| p.len()).sum::<usize>().max(1);
    let root = (squares / count).sqrt();
    if root.bits() == 0 {
        return refuse("a ring factor with no power");
    }
    let k = MATERIAL_BITS as i64 - (root.bits() as i64 - 1);
    let moved = i64::from(release_bits) + k;
    if moved < 0 {
        return refuse("a ring factor whose release falls below zero on the material's grain");
    }
    let scaled = parts
        .iter()
        .flat_map(|p| p.iter())
        .map(|&v| {
            let v = if k >= 0 { (v as i128) << k } else { release(v as i128, (-k) as u32) };
            fit32(v, "a ring factor's entry outgrew the material's 32-bit carrier")
        })
        .collect::<Result<Vec<i32>>>()?;
    Ok((scaled, moved as u32))
}

/// `x y` released by `bits`, exactly, half away from zero, through a wider integer when the product
/// leaves 128 bits; refused when the released value does.
fn wide_release(x: i128, y: i128, bits: u32) -> Result<i128> {
    if let Some(p) = x.checked_mul(y) {
        return Ok(release(p, bits));
    }
    let p = num_bigint::BigInt::from(x) * y;
    let half = if bits == 0 { num_bigint::BigInt::from(0) } else { num_bigint::BigInt::from(1) << (bits - 1) };
    let m = (p.magnitude().clone() + half.magnitude()) >> bits;
    let v = i128::try_from(num_bigint::BigInt::from(m)).map_err(|_| TowerError::Refused("a ring's covector outgrew its 128-bit carrier"))?;
    Ok(if p.sign() == num_bigint::Sign::Minus { -v } else { v })
}

/// The adjoint of [`ring_carry`]: the covector of the ring before the move from the covector after
/// it, `Mᵀ g` released from the moves' grain.
fn ring_carry_adjoint(m: [i128; 4], (gx, gy): (i128, i128)) -> (i128, i128) {
    let [lr, li, br, bi] = m;
    (release((lr + br) * gx + (li + bi) * gy, MOVE_BITS), release((bi - li) * gx + (lr - br) * gy, MOVE_BITS))
}

/// [agent-inferred, October 25] **The ring's hand after a move**: the orientation of the moves
/// composed since the ring's last restart. A move `h ↦ λh + βh̄` is the real map of determinant
/// `|λ|² − |β|²`: where that is positive it keeps the hand, where negative it reverses it (a
/// reflection, the dyad `U` of the mathematics thread's
/// [newline closure record](../../../../research/records/2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md),
/// §8), and where it is zero the move collapses the ring onto a line or the origin, so the
/// composite has no orientation and the ring restarts in the given hand. The ring is read in its
/// own hand, `(Re h, ±Im h)` ([`RingFace::advance`]): a turn met after a reflection is then read
/// turning the other way, as `a − b` is `a + b` with the second operand's turn reversed.
pub fn hand_after(m: [i128; 4], hand: bool) -> bool {
    let [lr, li, br, bi] = m;
    match (lr * lr + li * li).cmp(&(br * br + bi * bi)) {
        std::cmp::Ordering::Greater => hand,
        std::cmp::Ordering::Less => !hand,
        std::cmp::Ordering::Equal => false,
    }
}

/// The ring carried by one move `h ↦ λ h + β h̄`, `m = [Re λ, Im λ, Re β, Im β]` on `2^(−30)`.
pub fn ring_carry(m: [i128; 4], (re, im): (i128, i128)) -> (i128, i128) {
    let [lr, li, br, bi] = m;
    (release((lr + br) * re + (bi - li) * im, MOVE_BITS), release((li + bi) * re + (lr - br) * im, MOVE_BITS))
}

/// [definition; agent-inferred, October 25] **The resident ring face**: founded ring ranks
/// ([`RingRank`]) riding mode `mode` of level `level`, carried by every stream beside its modes
/// ([`TowerState::ring`]) and read by the tower's face through its pair contact with the top face,
///
/// ```text
/// q_t = (Re r_t, Im r_t) released by read_shift
/// ρ_t = 2^16 q_t / ‖q_t‖_rms                       (each rank's read as a ratio to its own power)
/// x̂_t = (2^16 x_t / ‖x_t‖_rms, 2^16)               (the top face the readout reads, and its unit)
/// z_t += W (x̂_t ⊗ ρ_t)
/// ```
///
/// `W` (`A × (d + 1)·2R`) opens at zero, so a joined tower opens on the tower it was joined to,
/// and is then founded on the passage it is joined on ([`Tower::open_ring_readout`]) and moved by
/// the section's covector. The ring's factors `a`, `b` and `g` are founded, carried into the
/// material at the join on its grain ([`factor_on_material`]) and moved by the same covector: the
/// ring reads the level's carried face and rides the mode's move, and the covector its face returns
/// reaches the face, the move and the factors that push from them ([`RingFace::reverse`]). Held,
/// the factors kept reading a face the tower had re-encoded under them: one block pass took the
/// founded ring's own read of the held-out units at a sum's second operand from 379 to 64 of 495
/// (record `2026-10-24_THE_TOWER_HEARS…`, "The ring's readout is a pair contact with the top
/// face"). It is
/// placed after its level's move and read at the face, not lifted into the level's input: the
/// moves it rides are keyed by that input, so a lift there would read the ring before it is formed.
///
/// A ring's reading is its turn: the units of a sum are a phase of the ring, and the ring's size
/// is its loudness, which varies by orders of magnitude between media (on the training text the
/// largest read was `2^9` times the read at a held-out sum's units). Each rank's face is therefore
/// its read as a ratio to its own power, the law the tower's own read obeys ([`ratio_to_power`],
/// "The read's carrier"): its scale is a gauge, and the covector the face returns turns the ring
/// and does not swell it ([`ratio_adjoint`]). A face fitted to the passage's largest read left the
/// readout reading a sum's units at `2^(−9)` of its reach, and one pass over the arithmetic made
/// the tower worse beside the ring than without it (69 against 72 of 495 at the units held out).
///
/// The readout is a pair contact because a ring's phase is news at one cell of a line and not at
/// the others: after a sum's second operand the ring holds the units' turn through `=` and the
/// result's other digits, and only the top face knows which cell codes the units. Read on the
/// joined tower with the tower held, a readout of `ρ` alone reads the held-out sums' units in 96 of
/// 495 and one through `x̂ ⊗ ρ` in about 300 (record `2026-10-24_THE_TOWER_HEARS…`, "The ring's
/// readout is a pair contact with the top face").
///
/// `b` is read over the encoding the ring was founded on, `E₀`, held with it: each class's pool is
/// generated from `b` and `E₀` whenever the material is read (a navigator's resident face, never a
/// stored table).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RingFace {
    level: usize,
    mode: usize,
    /// Each rank's releases of `a`, `b` and `g`, its push shift and its read shift, for its factors
    /// on the material's grain.
    shifts: Vec<([u32; 3], u32, u32)>,
    /// `E₀`, `A × d` on `2^(−16)`.
    opening: Vec<i32>,
    /// The founded factors on the material's grain, rank by rank `(a₀, a₁, b₀, b₁, g)`, until the
    /// join carries them into the material ([`Tower::join_ring_face`]); empty after it.
    founded: Vec<i32>,
    /// Each rank's founded pair moves ([`RingFace::move_at`]), `(prev, cur, [Re λ, Im λ, Re β,
    /// Im β])` on `2^(−30)`, strictly ascending by pair; a rank's table is empty when it rides its
    /// mode at every cell. Ranks closed on different keys ride different tables beside one
    /// another on the one mode.
    moves: Vec<Vec<(usize, usize, [i64; 4])>>,
    /// The characters the readout reads each rank's turn through ([`RingFace::with_harmonics`]):
    /// `1` reads the turn `ρ` alone.
    harmonics: usize,
    /// Each rank's restarting class ([`RingFace::with_restarts`]), when it has one.
    restarts: Vec<Option<usize>>,
}

/// [agent-inferred, October 25] `|λ| + |β| < 1` on the moves' grain, decided exactly: with
/// `U = 2^30`, `L = |λ|²` and `B = |β|²`, it holds iff `B < U²` and `|λ| < U − |β|`, that is
/// `2U|β| < U² + B − L` with the right side positive, squared: `4U²B < (U² + B − L)²`.
fn passive(m: [i64; 4]) -> bool {
    let u2 = num_bigint::BigInt::from(1u8) << (2 * MOVE_BITS);
    let sq = |a: i64, b: i64| num_bigint::BigInt::from(a) * a + num_bigint::BigInt::from(b) * b;
    let (l, b) = (sq(m[0], m[1]), sq(m[2], m[3]));
    if b >= u2 {
        return false;
    }
    let right = &u2 + &b - l;
    right > num_bigint::BigInt::from(0) && u2 * b * 4 < &right * &right
}

/// One rank's factors in the material: `a` (two parts over `2N`), `b` (two over `d + 1`) and `g`
/// (over `2N + 1`).
fn rank_material(d: &TowerDeclaration) -> usize {
    let (dims, hat) = (2 * d.modes, d.width + 1);
    3 * dims + 2 * hat + 1
}

impl RingFace {
    /// The face of `ranks` on mode `mode` of level `level`, founded on the encoding `opening`
    /// (`A × d`), each rank's factors carried onto the material's grain ([`factor_on_material`]).
    /// Refused unless every rank has `a` over `2N` coordinates, `b` over `d + 1` and `g` over
    /// `2N + 1`.
    ///
    /// `moves` are each rank's founded pair moves ([`RingFace::move_at`]), one table a rank (or
    /// none, every rank riding its mode), each strictly ascending by pair, each move over a class
    /// or the start (`prev ≤ A`) and a class (`cur < A`), and each passive, `|λ| + |β| < 1`: a
    /// boosting move leaves the ring without a bound, so it is refused.
    pub fn new(declaration: &TowerDeclaration, level: usize, mode: usize, ranks: Vec<RingRank>, opening: Vec<i32>, moves: Vec<Vec<(usize, usize, [i64; 4])>>) -> Result<Self> {
        let d = declaration;
        let (dims, w) = (2 * d.modes, d.width);
        if level >= d.levels || mode >= d.modes || ranks.is_empty() || opening.len() != d.alphabet * w {
            return refuse("a ring face needs a level and mode of the tower, a rank and an encoding of the tower's extent");
        }
        if ranks.iter().any(|r| r.a.iter().any(|a| a.len() != dims) || r.b.iter().any(|b| b.len() != w + 1) || r.g.len() != dims + 1) {
            return refuse("a ring rank needs a over the level's carried face, b over the class's face and g over the carried face and its unit");
        }
        let moves = if moves.is_empty() { vec![Vec::new(); ranks.len()] } else { moves };
        if moves.len() != ranks.len() {
            return refuse("a ring's pair moves are one table a rank");
        }
        if moves.iter().any(|t| t.iter().any(|&(prev, cur, _)| prev > d.alphabet || cur >= d.alphabet) || t.windows(2).any(|w| (w[0].0, w[0].1) >= (w[1].0, w[1].1))) {
            return refuse("a ring's pair moves are over a class or the start and a class, strictly ascending");
        }
        if moves.iter().flatten().any(|&(_, _, m)| !passive(m)) {
            return refuse("a ring's pair move that boosts (|λ| + |β| ≥ 1) leaves the ring without a bound");
        }
        let mut shifts = Vec::with_capacity(ranks.len());
        let mut founded = Vec::with_capacity(ranks.len() * rank_material(d));
        for rank in &ranks {
            let (a, ra) = factor_on_material(&[&rank.a[0], &rank.a[1]], rank.release[0])?;
            let (b, rb) = factor_on_material(&[&rank.b[0], &rank.b[1]], rank.release[1])?;
            let (g, rg) = factor_on_material(&[&rank.g], rank.release[2])?;
            founded.extend(a.into_iter().chain(b).chain(g));
            shifts.push(([ra, rb, rg], rank.push_shift, rank.read_shift));
        }
        let restarts = vec![None; shifts.len()];
        Ok(Self { level, mode, shifts, opening, founded, moves, harmonics: 1, restarts })
    }

    /// [agent-inferred, October 25] **The readout reads the turn through its characters**: each
    /// rank's face `ρ = |ρ| e^(iφ)` is read with its harmonics `q_h = |ρ| e^(ihφ)`, `h = 1..H`. A
    /// ring closed on a key of modulus `n` carries a class as a residue of `Z/n`, its turn
    /// `φ = 2πk/n`; the functions on `Z/n` are spanned by its characters `e^(ihφ)`, `|h| ≤ n/2`,
    /// and the conjugate harmonics are the same channels read through `W`'s imaginary columns, so
    /// `H = ⌊n/2⌋` lets the linear readout place every residue's class apart. One character reads
    /// the residue only through `cos(φ − φ_c)`, which separates neighbouring residues by
    /// `1 − cos(2π/n)` of the face; the record `2026-10-24_THE_TOWER_HEARS…`, "The closure founds
    /// the carriage", measures that ceiling. Refused at `H = 0`; and only before the face is joined
    /// (the readout's extent follows it).
    pub fn with_harmonics(mut self, harmonics: usize) -> Result<Self> {
        if harmonics == 0 || self.founded.is_empty() {
            return refuse("a ring face reads one or more harmonics, set before it is joined");
        }
        self.harmonics = harmonics;
        Ok(self)
    }

    /// The characters the readout reads each rank's turn through ([`RingFace::with_harmonics`]).
    pub fn harmonics(&self) -> usize {
        self.harmonics
    }

    /// [agent-inferred, October 25] **The hand's restart**: at each arrival of rank `r`'s class
    /// `restarts[r]`, after its move, the ring is re-based into the hand it reads,
    /// `h ↦ (Re h, o Im h)` and `o ↦ +` ([`hand_after`]). Its read at that cell is unchanged (it is
    /// that read); a turn met afterwards counts with the restored hand. A reflection reverses the
    /// hand and a restart restores it only where it is reversed, so a reflection between restarts
    /// reverses exactly the turns met between them: `a − b = c` read with `−` reflecting and `=`
    /// restarting turns the subtrahend's pairs back and the result's forward, as `a + b = c` turns
    /// them all forward (the mathematics thread's scratch reading, October 25: on sums and
    /// differences together the closure then has torsion `2·5·11`, where a reflection alone leaves
    /// `2·5`). A collapsing move restarts the ring with its hand; this restarts only the hand.
    /// Refused unless one class or none a rank; a class outside the alphabet never arrives, and
    /// the join and the text refuse one.
    pub fn with_restarts(mut self, restarts: Vec<Option<usize>>) -> Result<Self> {
        if restarts.len() != self.shifts.len() {
            return refuse("a ring's restarts are one class or none a rank");
        }
        self.restarts = restarts;
        Ok(self)
    }

    /// Each rank's restarting class ([`RingFace::with_restarts`]).
    pub fn restarts(&self) -> &[Option<usize>] {
        &self.restarts
    }

    /// [agent-inferred, October 25] **The move the ring makes** when `cur` arrives after `prev`
    /// (the seam, the start `A` at rest): its founded pair move, or the mode's move `m` where the
    /// founding did not meet the pair. A pair move is keyed by the seam because a relation that is
    /// known only at a crossing reads the byte before it: a sum's units are the product of the
    /// operands' units turns, and an operand's units digit is the seam at the next crossing (the
    /// record `2026-10-24_THE_TOWER_HEARS…`, "The readout founded to its precision, and the lap that
    /// undoes it"). The pair moves are held with the face: founded to their precision on a passage,
    /// a lap over that passage founds nothing in them, so their covector is not deposited.
    pub fn move_at(&self, rank: usize, prev: usize, cur: usize, m: [i128; 4]) -> [i128; 4] {
        self.pair_move(rank, prev, cur).unwrap_or(m)
    }

    /// Each rank's move at the cell ([`RingFace::move_at`]).
    pub fn moves_at(&self, prev: usize, cur: usize, m: [i128; 4]) -> Vec<[i128; 4]> {
        (0..self.moves.len()).map(|r| self.move_at(r, prev, cur, m)).collect()
    }

    /// Rank `rank`'s founded pair move at `(prev, cur)`, when its founding met the pair.
    fn pair_move(&self, rank: usize, prev: usize, cur: usize) -> Option<[i128; 4]> {
        let table = &self.moves[rank];
        table.binary_search_by_key(&(prev, cur), |&(p, c, _)| (p, c)).ok().map(|i| table[i].2.map(i128::from))
    }

    /// Each rank's founded pair moves ([`RingFace::move_at`]).
    pub fn pair_moves(&self) -> &[Vec<(usize, usize, [i64; 4])>] {
        &self.moves
    }

    /// Each rank's factors read from the material `factors` (this face's family, rank by rank),
    /// widened to the rank's carriers.
    fn ranks_of(&self, d: &TowerDeclaration, factors: &[i32]) -> Vec<RingRank> {
        let (dims, hat) = (2 * d.modes, d.width + 1);
        let wide = |v: &[i32]| -> Vec<i64> { v.iter().map(|&x| x as i64).collect() };
        factors
            .chunks_exact(rank_material(d))
            .zip(&self.shifts)
            .map(|(m, &(release, push_shift, read_shift))| RingRank {
                a: [wide(&m[..dims]), wide(&m[dims..2 * dims])],
                b: [wide(&m[2 * dims..2 * dims + hat]), wide(&m[2 * dims + hat..2 * dims + 2 * hat])],
                g: wide(&m[2 * dims + 2 * hat..]),
                release,
                push_shift,
                read_shift,
            })
            .collect()
    }

    /// Each class's pool, rank by rank, `pools[u · R + rank]`, generated from `b` and `E₀`.
    fn pools_of(&self, width: usize, ranks: &[RingRank]) -> Vec<(i128, i128)> {
        let alphabet = self.opening.len() / width;
        let mut pools = Vec::with_capacity(alphabet * ranks.len());
        for u in 0..alphabet {
            let mut hat: Vec<i64> = self.opening[u * width..(u + 1) * width].iter().map(|&e| e as i64).collect();
            hat.push(1 << FACE_BITS);
            pools.extend(ranks.iter().map(|r| r.pool(&hat)));
        }
        pools
    }

    /// The count of ranks `R` (the readout reads [`RingFace::channels`], `(d + 1)·2RH`).
    pub fn ranks(&self) -> usize {
        self.shifts.len()
    }

    /// The level and the mode the ring rides.
    pub fn placement(&self) -> (usize, usize) {
        (self.level, self.mode)
    }

    /// The readout's channels over a tower of width `w`: the top face's ratio and its unit
    /// (`w + 1`) by the ring's `2R` turns, each with its `H` harmonics.
    pub fn channels(&self, width: usize) -> usize {
        (width + 1) * 2 * self.shifts.len() * self.harmonics
    }

    /// The ring's pair read with the top face, `φ = x̂ ⊗ ρ` released to `2^(−16)` (row `j` of `x̂`
    /// by column `k` of `ρ`), with `x̂ = (top / ‖top‖_rms, 1)` on `2^(−16)`. Returns `φ`, the top's
    /// ratio (without its unit) and its scale.
    pub fn pair_read(top: &[i32], rho: &[i32]) -> Result<(Vec<i32>, Vec<i32>, i128)> {
        let wide: Vec<i64> = top.iter().map(|&v| v as i64).collect();
        let (hat, scale) = ratio_to_power(&wide)?;
        let mut phi = Vec::with_capacity((hat.len() + 1) * rho.len());
        for x in hat.iter().map(|&v| v as i128).chain(std::iter::once(1i128 << FACE_BITS)) {
            for &r in rho {
                phi.push(fit32(release(x * r as i128, FACE_BITS), "a ring's pair read outgrew its 32-bit carrier")?);
            }
        }
        Ok((phi, hat, scale))
    }

    /// One cell: each rank's ring carried by its move `m[r]` (its pair move or the mode's) and
    /// pushed from the carried face `s` and the arriving class `u`, with the factors `ranks` and
    /// their pools `pools` read from the material ([`Reaches`]); each rank's hand follows its move
    /// ([`hand_after`]), and a rank whose restarting class `u` is re-based into the hand it reads
    /// ([`RingFace::with_restarts`]). Returns each rank's read in its own hand, `(Re h, ±Im h)`,
    /// released by its `read_shift` (the founding's reading).
    #[allow(clippy::too_many_arguments)]
    fn advance(ranks: &[RingRank], pools: &[(i128, i128)], restarts: &[Option<usize>], ring: &mut [(i128, i128)], hands: &mut [bool], s: &[i64], u: usize, m: &[[i128; 4]]) -> Result<Vec<i64>> {
        let k = ranks.len();
        let mut read = Vec::with_capacity(2 * k);
        for (r, ((h, o), rank)) in ring.iter_mut().zip(hands.iter_mut()).zip(ranks).enumerate() {
            let (alpha, gamma) = rank.state_factors(s);
            let v = rank.push(alpha, pools[u * k + r], gamma)?;
            let carried = ring_carry(m[r], *h);
            *h = (carried.0 + v.0, carried.1 + v.1);
            *o = hand_after(m[r], *o);
            let im = fit64(release(h.1, rank.read_shift))?;
            read.push(fit64(release(h.0, rank.read_shift))?);
            read.push(if *o { -im } else { im });
            if *o && restarts[r] == Some(u) {
                *h = (h.0, -h.1);
                *o = false;
            }
        }
        Ok(read)
    }

    /// [agent-inferred, October 25] **The ring's reverse** over a section: the covector its face
    /// returns reaches the carried face `ŝ_t` it was pushed from, the move `(λ_t, β_t)` each rank
    /// rode, and the factors `a`, `b` and `g` that pushed it (`ranks`, read from the material, with
    /// their pools); the encoding `E₀` the pools read is held. `ring[t]` is each rank's ring after
    /// cell `t` and `opening` before the first; `faces[t]` is `ŝ_t`; `moves[t]` each rank's move
    /// (its pair move or the mode's); `hands` each rank's hand before the first cell, each later
    /// hand following the moves ([`hand_after`]) and the restarts ([`RingFace::with_restarts`]: a
    /// restart's re-basing `(x, y) ↦ (x, o y)` carries the covector after it back the same way);
    /// `g_rho[t]` the covector of each rank's read `q_t`, read in
    /// the rank's own hand `o_t` (`Vᵀ dz` carried back
    /// through the ratio by [`ratio_adjoint`], on the face's convention: `2^40` per unit of the
    /// read's grain). Per rank, with `σ = read_shift` and `P = push_shift`,
    ///
    /// ```text
    /// G_t = (g_ρx(t), o_t g_ρy(t)) + Mᵀ_(t+1) G_(t+1)        (2^(40+σ) per unit of r; o_t = ±1)
    /// ∂ŝ_t = Re(conj(G_t) ∂v_t/∂ŝ_t) 2^(−σ)                  (the modes' convention, per unit of ŝ)
    /// ∂(λ_t, β_t) = (x gx + y gy, x gy − y gx, x gx − y gy, x gy + y gx) 2^(8−σ)   at r_(t−1) = (x, y)
    /// e_t = conj(G_t) β_t γ_t 2^(−P−σ),  h_t = conj(G_t) α_t γ_t 2^(−P−σ),  f_t = Re(conj(G_t) α_t β_t) 2^(−P−σ)
    /// ∂a_j = Σ_t (Re e_t, −Im e_t) ŝ_(t,j),  ∂b_j = Σ_t (Re h_t, −Im h_t) x̂_(t,j),  ∂g_j = Σ_t f_t (ŝ_t, 2^16)_j
    /// ```
    ///
    /// the moves on the modes' own convention for their moves' covectors (`h_(t−1)` on `2^(−24)`
    /// against a covector per unit of the face's `2^(−16)`), and each factor's sum taken whole and
    /// then carried to the material's convention, `2^40` per unit of its grain `2^(−24)`, by
    /// `2^(24 − release)`. Returns `∂ŝ_t` per cell, each rank's `∂(λ_t, β_t)` per cell (cell `t`'s
    /// rank `r` at `t·R + r`) and the factors' covector in the material's order (rank by rank
    /// `a₀, a₁, b₀, b₁, g`).
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn reverse(
        &self,
        ranks: &[RingRank],
        pools: &[(i128, i128)],
        opening: &[(i128, i128)],
        hands: &[bool],
        ring: &[&[(i128, i128)]],
        faces: &[Vec<i64>],
        classes: &[usize],
        moves: &[Vec<[i128; 4]>],
        g_rho: &[Vec<i64>],
    ) -> Result<(Vec<Vec<i64>>, Vec<[i128; 4]>, Vec<i128>)> {
        let (k, n) = (ranks.len(), faces.len());
        let dims = faces.first().map_or(0, Vec::len);
        let alphabet = pools.len() / k.max(1);
        let width = self.opening.len() / alphabet.max(1);
        let wide = || TowerError::Refused("a ring's covector outgrew its 128-bit carrier");
        let add = |slot: &mut i128, v: Option<i128>| -> Result<()> {
            *slot = v.and_then(|v| slot.checked_add(v)).ok_or_else(wide)?;
            Ok(())
        };
        let mut d_face = vec![vec![0i128; dims]; n];
        let mut d_moves = vec![[0i128; 4]; n * k];
        let mut d_factors = Vec::with_capacity(k * (3 * dims + 2 * (width + 1) + 1));
        for (r, rank) in ranks.iter().enumerate() {
            let sigma = rank.read_shift;
            let to_moves = |x: i128, y: i128| -> Result<i128> { if sigma >= 8 { wide_release(x, y, sigma - 8) } else { x.checked_mul(y).and_then(|p| p.checked_mul(1 << (8 - sigma))).ok_or_else(wide) } };
            let [ra, rb, rg] = rank.release;
            let (mut da, mut db, mut dg) = ([vec![0i128; dims], vec![0i128; dims]], [vec![0i128; width + 1], vec![0i128; width + 1]], vec![0i128; dims + 1]);
            // The hand after each cell's move, from the opening's: the read is (Re h, o_t Im h); a
            // restart then re-bases a reversed ring, (x, y) ↦ (x, −y), and restores the hand.
            let own: Vec<(bool, bool)> = moves
                .iter()
                .zip(classes)
                .scan(hands[r], |o, (m, &u)| {
                    let read = hand_after(m[r], *o);
                    let rebased = read && self.restarts[r] == Some(u);
                    *o = read && !rebased;
                    Some((read, rebased))
                })
                .collect();
            let mut g = (0i128, 0i128);
            for t in (0..n).rev() {
                let back = if t + 1 < n { ring_carry_adjoint(moves[t + 1][r], g) } else { (0, 0) };
                let back = if own[t].1 { (back.0, -back.1) } else { back };
                let own_t = own[t].0;
                let gy = g_rho[t][2 * r + 1] as i128;
                g = (g_rho[t][2 * r] as i128 + back.0, if own_t { -gy } else { gy } + back.1);
                let (gx, gy) = g;
                let (x, y) = if t == 0 { opening[r] } else { ring[t - 1][r] };
                let terms = [(x, gx, y, gy, 1), (x, gy, y, gx, -1), (x, gx, y, gy, -1), (x, gy, y, gx, 1)];
                for (slot, (p, q, u, v, sign)) in d_moves[t * k + r].iter_mut().zip(terms) {
                    *slot = slot.checked_add(to_moves(p, q)?.checked_add(sign * to_moves(u, v)?).ok_or_else(wide)?).ok_or_else(wide)?;
                }
                // conj(G) β and conj(G) α, then their products with γ and α, released by the push and σ.
                let s = &faces[t];
                let (alpha, gamma) = rank.state_factors(s);
                let beta = pools[classes[t] * k + r];
                let cb = (gx.checked_mul(beta.0).zip(gy.checked_mul(beta.1)).and_then(|(a, b)| a.checked_add(b)).ok_or_else(wide)?, gx.checked_mul(beta.1).zip(gy.checked_mul(beta.0)).and_then(|(a, b)| a.checked_sub(b)).ok_or_else(wide)?);
                let ca = (gx.checked_mul(alpha.0).zip(gy.checked_mul(alpha.1)).and_then(|(a, b)| a.checked_add(b)).ok_or_else(wide)?, gx.checked_mul(alpha.1).zip(gy.checked_mul(alpha.0)).and_then(|(a, b)| a.checked_sub(b)).ok_or_else(wide)?);
                let total = rank.push_shift + sigma;
                let e = (wide_release(cb.0, gamma, total)?, wide_release(cb.1, gamma, total)?);
                let h = (wide_release(ca.0, gamma, total)?, wide_release(ca.1, gamma, total)?);
                let f = wide_release(cb.0, alpha.0, total)?.checked_sub(wide_release(cb.1, alpha.1, total)?).ok_or_else(wide)?;
                for (j, slot) in d_face[t].iter_mut().enumerate() {
                    let through_a = release(e.0.checked_mul(rank.a[0][j] as i128).zip(e.1.checked_mul(rank.a[1][j] as i128)).and_then(|(p, q)| p.checked_sub(q)).ok_or_else(wide)?, ra);
                    let through_g = release(f.checked_mul(rank.g[j] as i128).ok_or_else(wide)?, rg);
                    *slot = slot.checked_add(through_a).and_then(|v| v.checked_add(through_g)).ok_or_else(wide)?;
                    let sj = s[j] as i128;
                    add(&mut da[0][j], e.0.checked_mul(sj))?;
                    add(&mut da[1][j], e.1.checked_mul(-sj))?;
                    add(&mut dg[j], f.checked_mul(sj))?;
                }
                add(&mut dg[dims], f.checked_mul(1 << FACE_BITS))?;
                let u = classes[t];
                let hat = self.opening[u * width..(u + 1) * width].iter().map(|&v| v as i128).chain(std::iter::once(1i128 << FACE_BITS));
                for (j, xj) in hat.enumerate() {
                    add(&mut db[0][j], h.0.checked_mul(xj))?;
                    add(&mut db[1][j], h.1.checked_mul(-xj))?;
                }
            }
            // Each sum on the material's convention: 2^40 per unit of 2^(−24), from the factor's release.
            let on_grain = |v: i128, bits: u32| -> Result<i128> {
                if bits >= MATERIAL_BITS { Ok(release(v, bits - MATERIAL_BITS)) } else { v.checked_mul(1 << (MATERIAL_BITS - bits)).ok_or_else(wide) }
            };
            for (part, bits) in [(&da[0], ra), (&da[1], ra), (&db[0], rb), (&db[1], rb), (&dg, rg)] {
                for &v in part.iter() {
                    d_factors.push(on_grain(v, bits)?);
                }
            }
        }
        let d_face = collect_exact(d_face.into_iter().map(|row| collect_exact(row.into_iter().map(fit64))))?;
        Ok((d_face, d_moves, d_factors))
    }

    /// Each rank's read as a ratio to its own power, on `2^(−16)`, then its harmonics
    /// ([`RingFace::with_harmonics`]), rank by rank `ρ, q_2, …, q_H`, with each rank's scale.
    fn face(&self, read: &[i64]) -> Result<(Vec<i32>, Vec<i128>)> {
        let mut face = Vec::with_capacity(read.len() * self.harmonics);
        let mut scales = Vec::with_capacity(self.shifts.len());
        for q in read.chunks(2) {
            let (rho, scale) = ratio_to_power(q)?;
            face.extend(harmonics_of(&rho, self.harmonics)?);
            scales.push(scale);
        }
        Ok((face, scales))
    }

    /// The face as text: its placement and each rank's shifts, then `E₀`, then, when any rank has
    /// pair moves, one line a rank (`ring-moves N prev,cur,Re λ,Im λ,Re β,Im β …`, `N = 0` for a
    /// rank riding its mode), `ring-harmonics H` past one character and `ring-restarts c|- …` when a
    /// rank restarts its hand. Its factors are the material's, written with it.
    fn to_text(&self) -> String {
        let join = |xs: &mut dyn Iterator<Item = String>| xs.collect::<Vec<_>>().join(" ");
        let shifts = join(&mut self.shifts.iter().map(|([ra, rb, rg], push, read)| format!("{ra},{rb},{rg},{push},{read}")));
        let mut s = format!("ring-face {} {} {} {shifts}\n{}\n", self.level, self.mode, self.shifts.len(), join(&mut self.opening.iter().map(|v| v.to_string())));
        if self.moves.iter().any(|t| !t.is_empty()) {
            for table in &self.moves {
                let moves = join(&mut std::iter::once(format!("ring-moves {}", table.len())).chain(table.iter().map(|(p, c, m)| format!("{p},{c},{},{},{},{}", m[0], m[1], m[2], m[3]))));
                s.push_str(&format!("{moves}\n"));
            }
        }
        if self.harmonics > 1 {
            s.push_str(&format!("ring-harmonics {}\n", self.harmonics));
        }
        if self.restarts.iter().any(Option::is_some) {
            s.push_str(&format!("ring-restarts {}\n", join(&mut self.restarts.iter().map(|c| c.map_or("-".to_string(), |c| c.to_string())))));
        }
        s
    }

    fn from_text(head: &str, opening: &str, moves: &[&str], harmonics: Option<&str>, restarts: Option<&str>, declaration: &TowerDeclaration) -> Result<Self> {
        let bad = TowerError::Refused("not a ring face's text");
        let words: Vec<&str> = head.split(' ').collect();
        if words.len() < 4 || words[0] != "ring-face" {
            return Err(bad);
        }
        let num = |s: &str| s.parse::<usize>().map_err(|_| bad.clone());
        let (level, mode, k) = (num(words[1])?, num(words[2])?, num(words[3])?);
        if words.len() != 4 + k || k == 0 {
            return Err(bad);
        }
        let opening: Vec<i32> = opening.split(' ').map(|s| s.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
        let d = declaration;
        if level >= d.levels || mode >= d.modes || opening.len() != d.alphabet * d.width {
            return Err(bad);
        }
        let mut shifts = Vec::with_capacity(k);
        for word in &words[4..] {
            let s: Vec<u32> = word.split(',').map(|v| v.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
            if s.len() != 5 {
                return Err(bad);
            }
            shifts.push(([s[0], s[1], s[2]], s[3], s[4]));
        }
        if !moves.is_empty() && moves.len() != k {
            return Err(bad);
        }
        let mut tables: Vec<Vec<(usize, usize, [i64; 4])>> = vec![Vec::new(); k];
        for (line, table) in moves.iter().zip(tables.iter_mut()) {
            let words: Vec<&str> = line.split(' ').collect();
            if words.len() < 2 || words[0] != "ring-moves" || words[1].parse::<usize>().ok() != Some(words.len() - 2) {
                return Err(bad);
            }
            for word in &words[2..] {
                let v: Vec<i64> = word.split(',').map(|x| x.parse().map_err(|_| bad.clone())).collect::<Result<_>>()?;
                if v.len() != 6 || v[0] < 0 || v[1] < 0 {
                    return Err(bad);
                }
                table.push((v[0] as usize, v[1] as usize, [v[2], v[3], v[4], v[5]]));
            }
        }
        let moves = tables;
        if moves.iter().any(|t| t.iter().any(|&(prev, cur, _)| prev > d.alphabet || cur >= d.alphabet) || t.windows(2).any(|w| (w[0].0, w[0].1) >= (w[1].0, w[1].1)) || t.iter().any(|&(_, _, m)| !passive(m))) {
            return Err(bad);
        }
        let harmonics = match harmonics.map(|line| line.strip_prefix("ring-harmonics ").and_then(|h| h.parse::<usize>().ok())) {
            None => 1,
            Some(Some(h)) if h > 1 => h,
            Some(_) => return Err(bad),
        };
        let restarts_line = restarts.is_some();
        let restarts: Vec<Option<usize>> = match restarts.map(|line| line.strip_prefix("ring-restarts ")) {
            None => vec![None; k],
            Some(Some(words)) => words.split(' ').map(|w| if w == "-" { Ok(None) } else { w.parse::<usize>().ok().filter(|&c| c < d.alphabet).map(Some).ok_or(bad.clone()) }).collect::<Result<_>>()?,
            Some(None) => return Err(bad),
        };
        // A written restarts line names a restart (the text is canonical).
        if restarts.len() != k || (restarts_line && restarts.iter().all(Option::is_none)) {
            return Err(bad);
        }
        Ok(Self { level, mode, shifts, opening, founded: Vec::new(), moves, harmonics, restarts })
    }
}

/// [definition; agent-inferred with the mathematics thread, October 26] **The rotor**: a ring's
/// generator and modulator as one monomial move. A level's first modes are grouped in rings `R_k`,
/// each of a width `w_k` and a modulus `q_k` (the modes past the rings are still), and each
/// arriving class `u` steps ring `k` by its key `σ = σ(level, u, k) ∈ ℤ/w_k` and turns the ring's
/// mode `j` by its key `r = r(level, u, s_k + j) ∈ ℤ/q_k` before the level's move, `s_k` the ring's
/// first mode:
///
/// ```text
/// h'_(t−1) = T_t P^(σ_t) h_(t−1),   (T P^σ h)_(s_k + j) = e^(2πi r_(s_k + j)/q_k) h_(s_k + ((j + σ) mod w_k))
/// h_t      = λ_t ⊙ h' + β_t ⊙ conj(h') + γ_t ⊙ B x_t        (the level's own move, on h')
/// ```
///
/// Why (the records
/// `2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`,
/// its §11, and
/// `2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md`,
/// §5): reading a digit `d` maps a numeral `n ↦ 10 n + d`, and on a character
/// `χ_a(n) = e^(2πi a n/q)` that is `χ_a(10n + d) = χ_a(d) χ_(10a)(n)`: the turn `χ_a(d)` (the
/// modulator) and a step of the character's index `a ↦ 10a` (the generator, a translation of the
/// index). With mode `j` of a ring holding the character `c·10^j`, the step is the ring's cyclic
/// shift, which closes after `w` steps, `w` the order of 10 modulo `q` (9 → 1, 11 → 2, 101 → 4), and
/// the turn of mode `j` is `r = c·10^j·d mod q`; a unit of several digits steps by their count and
/// turns by the characters of their value. The step alone (the generator without the modulator) is
/// a clock of position: its modes hold sums of drives, never the product of turns a numeral is. The
/// Fourier chart exchanges the two (`F X = Z F`): the shift is a turn of the ring's harmonics, so
/// the step is a modulator in the dual chart and the turn a generator, one move read in two charts.
///
/// The turns are integer residues; each key's face `e^(2πi r/q)` on `2^(−30)` is resident, generated
/// once from the half turn's navigator by the exponential series and rounded into the unit disk. So
/// the move is a permutation times unimodular turns, and the passivity bound
/// `|h_t| ≤ ρ_t |h_(t−1)| + γ_t |B x_t|` holds unchanged up to the half grain of the turn's release
/// to the state's grain, as the move's own release (Lean `HNN/PassiveMode`: `passive_recursion`
/// proves the bound for any hand-over of modes and coefficients of modulus at most `ρ_max < 1`, and
/// `pumped_recursion` for the pumped step with `|α| + |β| ≤ ρ_max`; a turn `e` enters as `α e` and
/// `β ē`, which keeps both moduli). A mode turned by zero is carried exactly, so a class that turns
/// nothing steps its rings as a permutation, and with no ring, or every key zero, the rotor tower
/// reads every passage as its twin without the rotor (the opening). `σ` and `r` have no covector:
/// keys in `ℤ/w` and `ℤ/q` are located by loop closure, not by descent. The reverse
/// carries the mode covector back through the monomial's adjoint,
/// `G_h(t) = (Cᵀδr)⁻ + (T_(t+1) P^(σ_(t+1)))* (conj(λ_(t+1)) ⊙ G_h(t+1) + β_(t+1) ⊙ conj(G_h(t+1)))`,
/// mode `s_k + ((j + σ) mod w_k)` taking `e^(−2πi r/q)` times mode `s_k + j`'s, and every covector
/// that read `h_(t−1)` reads `h'_(t−1)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rotor {
    rings: Vec<RotorRing>,
    /// `σ`, level-major, then class, then ring, each below its ring's width.
    steps: Vec<u32>,
    /// `r`, level-major, then class, then moving mode, each below its ring's modulus.
    turns: Vec<u32>,
    levels: usize,
    alphabet: usize,
    modes: usize,
    /// Each moving mode's ring and the ring's first mode.
    places: Vec<(usize, usize)>,
    /// Each key's resident face `e^(2πi r/q)` on `2^(−30)`, aligned with `turns`.
    faces: Vec<(i128, i128)>,
}

/// A ring of the rotor: `width` modes, mode `j` holding the character `c·10^j` of a numeral modulo
/// `modulus`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RotorRing {
    pub width: usize,
    pub modulus: u32,
}

/// `e^(2πi r/q)` on `2^(−30)`: the angle read from the half turn's navigator thirty grains finer
/// (`half_turn`), taken in `(−π, π]`, the exponential series summed at the grain, and the face
/// rounded into the closed unit disk, its larger part released a grain toward zero until
/// `|e|² ≤ 1` (a turn keeps the passivity bound).
fn ring_face(r: u32, q: u32) -> (i128, i128) {
    ring_face_at(r, q, half_turn(2 * MOVE_BITS))
}

/// [`ring_face`] from the half turn `fine` on `2^(−60)`, held by the caller.
fn ring_face_at(r: u32, q: u32, fine: i128) -> (i128, i128) {
    let signed = if 2 * u64::from(r) <= u64::from(q) { i128::from(r) } else { i128::from(r) - i128::from(q) };
    let angle = div_nearest(2 * signed * fine, i128::from(q) << MOVE_BITS);
    let (mut a, mut b) = exp_series(0, angle);
    while a * a + b * b > 1i128 << (2 * MOVE_BITS) {
        if a.abs() >= b.abs() {
            a -= a.signum();
        } else {
            b -= b.signum();
        }
    }
    (a, b)
}

impl Rotor {
    /// The rotor of `rings` on a tower of `declaration`, with `steps` (level-major, then class, then
    /// ring, each below its ring's width) and `turns` (level-major, then class, then moving mode,
    /// each below its ring's modulus). Refused unless every ring holds a mode and a modulus above
    /// one, the rings fit in a level's modes, and there is one key for each level, class and ring,
    /// and for each level, class and moving mode.
    pub fn new(declaration: &TowerDeclaration, rings: Vec<RotorRing>, steps: Vec<u32>, turns: Vec<u32>) -> Result<Self> {
        let d = declaration;
        if rings.iter().any(|g| g.width == 0 || g.modulus < 2) {
            return refuse("a rotor's ring holds a mode and a modulus above one");
        }
        let mut places = Vec::new();
        for (k, g) in rings.iter().enumerate() {
            let first = places.len();
            places.extend((0..g.width).map(|_| (k, first)));
        }
        let moving = places.len();
        if moving > d.modes {
            return refuse("a rotor's rings that do not fit in a level's modes");
        }
        let keyed = d.levels * d.alphabet;
        if steps.len() != keyed * rings.len() || steps.chunks(rings.len().max(1)).any(|s| s.iter().zip(&rings).any(|(&s, g)| s as usize >= g.width)) {
            return refuse("a rotor holds one step below its ring's width for each level, class and ring");
        }
        if turns.len() != keyed * moving || turns.chunks(moving.max(1)).any(|r| r.iter().zip(&places).any(|(&r, &(k, _))| r >= rings[k].modulus)) {
            return refuse("a rotor holds one turn below its ring's modulus for each level, class and moving mode");
        }
        let mut resident = std::collections::BTreeMap::new();
        let faces = turns
            .iter()
            .enumerate()
            .map(|(i, &r)| {
                let q = rings[places[i % moving].0].modulus;
                *resident.entry((q, r)).or_insert_with(|| ring_face(r, q))
            })
            .collect();
        Ok(Self { rings, steps, turns, levels: d.levels, alphabet: d.alphabet, modes: d.modes, places, faces })
    }

    /// The rotor with no ring: the opening, which reads as the tower without it.
    pub fn opening(declaration: &TowerDeclaration) -> Self {
        Self { rings: Vec::new(), steps: Vec::new(), turns: Vec::new(), levels: declaration.levels, alphabet: declaration.alphabet, modes: declaration.modes, places: Vec::new(), faces: Vec::new() }
    }

    /// The rings, from a level's first mode.
    pub fn rings(&self) -> &[RotorRing] {
        &self.rings
    }

    /// The count of moving modes, the rings' widths summed: a level's first modes.
    pub fn moving(&self) -> usize {
        self.places.len()
    }

    /// The key `σ` of ring `ring` at level `level` when `class` arrives.
    pub fn step(&self, level: usize, class: usize, ring: usize) -> usize {
        self.steps[(level * self.alphabet + class) * self.rings.len() + ring] as usize
    }

    /// The key `r` of mode `mode` at level `level` when `class` arrives (zero past the rings).
    pub fn turn(&self, level: usize, class: usize, mode: usize) -> u32 {
        let moving = self.places.len();
        if mode < moving { self.turns[(level * self.alphabet + class) * moving + mode] } else { 0 }
    }

    /// The steps, level-major, then class, then ring.
    pub fn steps(&self) -> &[u32] {
        &self.steps
    }

    /// The turns, level-major, then class, then moving mode.
    pub fn turns(&self) -> &[u32] {
        &self.turns
    }

    /// Whether `class` steps and turns nothing at `level`.
    fn still(&self, level: usize, class: usize) -> bool {
        let (k, moving) = (self.rings.len(), self.places.len());
        let at = level * self.alphabet + class;
        self.steps[at * k..(at + 1) * k].iter().all(|&s| s == 0) && self.turns[at * moving..(at + 1) * moving].iter().all(|&r| r == 0)
    }

    /// The mode whose state mode `m` takes at `level` when `class` arrives: within its ring,
    /// `s_k + ((j + σ) mod w_k)`, and itself past the rings.
    pub fn source(&self, level: usize, class: usize, m: usize) -> usize {
        match self.places.get(m) {
            Some(&(k, first)) => first + (m - first + self.step(level, class, k)) % self.rings[k].width,
            None => m,
        }
    }

    /// `h' = T P^σ h` at `level` when `class` arrives: mode `s_k + j` takes mode
    /// `s_k + ((j + σ) mod w_k)` turned by its key's face, released to the state's grain (carried
    /// exactly where the key is zero).
    pub fn moved(&self, level: usize, class: usize, h: &[(i64, i64)]) -> Result<Vec<(i64, i64)>> {
        let moving = self.places.len();
        let at = (level * self.alphabet + class) * moving;
        let mut out = h.to_vec();
        for m in 0..moving {
            let (x, y) = h[self.source(level, class, m)];
            out[m] = if self.turns[at + m] == 0 {
                (x, y)
            } else {
                let (a, b) = self.faces[at + m];
                let (x, y) = (i128::from(x), i128::from(y));
                (fit64(release(a * x - b * y, MOVE_BITS))?, fit64(release(a * y + b * x, MOVE_BITS))?)
            };
        }
        Ok(out)
    }

    /// The covector of `h` from the covector `g` of `h' = T P^σ h`: mode `s_k + ((j + σ) mod w_k)`
    /// takes `e^(−2πi r/q)` times mode `s_k + j`'s (exactly where the key is zero), the modes past the
    /// rings their own.
    pub fn back(&self, level: usize, class: usize, g: &[(i128, i128)]) -> Vec<(i128, i128)> {
        let moving = self.places.len();
        let at = (level * self.alphabet + class) * moving;
        let mut out = g.to_vec();
        for m in 0..moving {
            let (x, y) = g[m];
            out[self.source(level, class, m)] = if self.turns[at + m] == 0 {
                (x, y)
            } else {
                let (a, b) = self.faces[at + m];
                (release(a * x + b * y, MOVE_BITS), release(a * y - b * x, MOVE_BITS))
            };
        }
        out
    }

    /// `rotor LEVELS ALPHABET MODES` and each ring as `WIDTH:MODULUS`, then the steps and the turns,
    /// one line each.
    fn to_text(&self) -> String {
        let join = |keys: &[u32]| keys.iter().map(u32::to_string).collect::<Vec<_>>().join(" ");
        let rings: String = self.rings.iter().map(|g| format!(" {}:{}", g.width, g.modulus)).collect();
        format!("rotor {} {} {}{rings}\n{}\n{}\n", self.levels, self.alphabet, self.modes, join(&self.steps), join(&self.turns))
    }

    fn from_text(head: &str, steps: &str, turns: &str, declaration: &TowerDeclaration) -> Result<Self> {
        let d = declaration;
        let bad = TowerError::Refused("a rotor's text that is not the tower's");
        let words: Vec<&str> = head.split(' ').collect();
        if words.len() < 4 || words[..4].join(" ") != format!("rotor {} {} {}", d.levels, d.alphabet, d.modes) {
            return Err(bad);
        }
        let rings = words[4..]
            .iter()
            .map(|w| {
                let (width, modulus) = w.split_once(':').ok_or(bad.clone())?;
                Ok(RotorRing { width: width.parse().map_err(|_| bad.clone())?, modulus: modulus.parse().map_err(|_| bad.clone())? })
            })
            .collect::<Result<Vec<_>>>()?;
        // A line of keys, each a count; an empty line holds none (a rotor without rings).
        let keys = |line: &str| -> Result<Vec<u32>> {
            if line.is_empty() {
                return Ok(Vec::new());
            }
            line.split(' ').map(|w| w.parse().map_err(|_| bad.clone())).collect()
        };
        Self::new(d, rings, keys(steps)?, keys(turns)?)
    }
}

/// [definition; agent-inferred, October 26] **The strands** (record
/// `2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES.md`,
/// §2). A stream carries three strands of residues on each ring `q_L` (the closure's torsion at
/// period `L`) and one orientation `o ∈ {+1, −1}`, the helical code's dyad: `USU = S⁻¹`, so a numeral
/// read between two reflections turns backwards. Each byte of an arriving class's word acts in turn:
///
/// ```text
/// located digit byte, turn θ_L:   turned   r_L ← μ_L r_L + o·θ_L     the numeral's character
///                                 stepped  r_L ← μ_L r_L             the generator alone
///                                 held     r_L ← r_L                 still
/// byte with a located key:        r'_s ← ±r_(src s) or 0, each strand;  o kept, flipped or set
/// any other byte:                 nothing moves
/// ```
///
/// `μ_L` is the located step's multiplier on ring `L` (the ratio of the located turns of
/// neighbouring modes). **No key adds two residues**: a key transfers, reflects or clears, so no
/// state holds a sum of two numerals. The faces `e^(2πi r/q_L)` of every strand on every ring,
/// strand-major, are read at their level's contacts beside the level's read (record §7): their two
/// parts `s` on the face's grain join `r̂ = r/‖r‖_rms` as ratio components, in its gauge, so no
/// level's power divides them,
///
/// ```text
/// a = W_a r̂ + W_sa s + b_a,     b = W_b r̂ + W_sb s + b_b,     v = a ⊙ b
/// ```
///
/// and a contact's product of two faces is the comparison of two strands
/// ([`Tower::open_strands_comparison`]), while a written digit is the readout's. The faces carry no
/// covector (residues have none; the turns, laws and keys are located by loop closure, as the
/// rotor's keys are); `W_sa` and `W_sb` take `δa ⊗ s` and `δb ⊗ s`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Strands {
    level: usize,
    rings: Vec<StrandRing>,
    laws: [StrandLaw; 3],
    /// Each located digit byte with its turn on every ring, ascending by byte.
    digits: Vec<(u8, Vec<u32>)>,
    /// Each byte with a located key and the key, ascending by byte.
    keys: Vec<(u8, StrandKey)>,
    /// Each class's bytes, in the order the boundary codec reads them.
    words: Vec<Vec<u8>>,
    levels: usize,
    alphabet: usize,
    modes: usize,
    /// The half turn on `2^(−60)`, the faces' resident navigator.
    half_turn: i128,
}

/// A ring of the strands: residues modulo `modulus`, a digit stepping them by `multiplier`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StrandRing {
    pub modulus: u32,
    pub multiplier: u32,
}

/// A strand's law at a digit ([`Strands`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum StrandLaw {
    /// `r ← μ r + o·θ`: the numeral's character.
    Turned,
    /// `r ← μ r`: the generator alone.
    Stepped,
    /// `r ← r`: still.
    Held,
}

impl StrandLaw {
    pub const ALL: [Self; 3] = [Self::Turned, Self::Stepped, Self::Held];

    /// The residue `r` after a digit of turn `theta` on `ring`, read on the reversed sheet or not.
    pub fn at_digit(self, r: u32, theta: u32, ring: StrandRing, reversed: bool) -> u32 {
        let q = u64::from(ring.modulus);
        let stepped = u64::from(r) * u64::from(ring.multiplier) % q;
        match self {
            Self::Turned => {
                let turn = if reversed { (q - u64::from(theta) % q) % q } else { u64::from(theta) % q };
                ((stepped + turn) % q) as u32
            }
            Self::Stepped => stepped as u32,
            Self::Held => r,
        }
    }

    /// The law's name as the strands' text writes it.
    pub fn name(self) -> &'static str {
        match self {
            Self::Turned => "turned",
            Self::Stepped => "stepped",
            Self::Held => "held",
        }
    }

    fn named(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|law| law.name() == name)
    }
}

/// What a key does to the orientation ([`Strands`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Sheet {
    Kept,
    Flipped,
    /// Set to `+1`.
    Plus,
    /// Set to `−1`.
    Minus,
}

impl Sheet {
    pub const ALL: [Self; 4] = [Self::Kept, Self::Flipped, Self::Plus, Self::Minus];

    /// The orientation after the key (`true` on the reversed sheet).
    pub fn after(self, reversed: bool) -> bool {
        match self {
            Self::Kept => reversed,
            Self::Flipped => !reversed,
            Self::Plus => false,
            Self::Minus => true,
        }
    }

    fn letter(self) -> char {
        match self {
            Self::Kept => 'k',
            Self::Flipped => 'f',
            Self::Plus => 'p',
            Self::Minus => 'm',
        }
    }
}

/// A located key ([`Strands`]): strand `s` takes `source[s]`, which is `0` (zero, `E(0)`), `k`
/// (strand `k − 1`) or `−k` (its reflection), and the orientation takes `sheet`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StrandKey {
    pub source: [i8; 3],
    pub sheet: Sheet,
}

impl StrandKey {
    /// The key that moves nothing.
    pub const IDENTITY: Self = Self { source: [1, 2, 3], sheet: Sheet::Kept };

    /// Every key: the seven sources of each strand (`0`, `±1`, `±2`, `±3`) and the four sheets,
    /// 1,372 in a fixed order, the identity first.
    pub fn all() -> Vec<Self> {
        const SOURCES: [i8; 7] = [0, 1, -1, 2, -2, 3, -3];
        let mut keys = vec![Self::IDENTITY];
        for &a in &SOURCES {
            for &b in &SOURCES {
                for &c in &SOURCES {
                    for sheet in Sheet::ALL {
                        let key = Self { source: [a, b, c], sheet };
                        if key != Self::IDENTITY {
                            keys.push(key);
                        }
                    }
                }
            }
        }
        keys
    }

    /// The rows it changes: each strand that takes anything but itself, and the sheet unless kept.
    pub fn changes(&self) -> usize {
        self.source.iter().enumerate().filter(|&(s, &v)| v != s as i8 + 1).count() + usize::from(self.sheet != Sheet::Kept)
    }

    /// The residues `r` on a ring of `q` after the key.
    pub fn apply(&self, r: [u32; 3], q: u32) -> [u32; 3] {
        self.source.map(|v| match v {
            0 => 0,
            v if v > 0 => r[v as usize - 1],
            v => (q - r[(-v) as usize - 1] % q) % q,
        })
    }

    fn text(&self) -> String {
        format!("{},{},{}:{}", self.source[0], self.source[1], self.source[2], self.sheet.letter())
    }

    fn from_text(text: &str) -> Option<Self> {
        let (sources, sheet) = text.split_once(':')?;
        let source: Vec<i8> = sources.split(',').map(|v| v.parse().ok()).collect::<Option<_>>()?;
        let sheet = Sheet::ALL.into_iter().find(|s| sheet.len() == 1 && sheet.starts_with(s.letter()))?;
        Some(Self { source: source.try_into().ok()?, sheet })
    }
}

impl Strands {
    /// The strands read at the contacts of `level` of a tower of `declaration`: the rings, the three
    /// laws, the digit bytes' turns (one below each ring's modulus), the keyed bytes' keys, and one
    /// word for each class. Refused unless the level is the tower's and there is a ring, every ring
    /// has a modulus above one and a multiplier below it, the bytes ascend and no byte is both a
    /// digit and keyed, and every key's sources name a strand or zero.
    pub fn new(declaration: &TowerDeclaration, level: usize, rings: Vec<StrandRing>, laws: [StrandLaw; 3], digits: Vec<(u8, Vec<u32>)>, keys: Vec<(u8, StrandKey)>, words: Vec<Vec<u8>>) -> Result<Self> {
        let d = declaration;
        if level >= d.levels || rings.is_empty() {
            return refuse("strands on a level the tower does not have, or on no ring");
        }
        if rings.iter().any(|g| g.modulus < 2 || g.multiplier >= g.modulus) {
            return refuse("a strands' ring holds a modulus above one and a multiplier below it");
        }
        if words.len() != d.alphabet {
            return refuse("strands hold one word for each class");
        }
        if digits.windows(2).any(|p| p[0].0 >= p[1].0) || keys.windows(2).any(|p| p[0].0 >= p[1].0) {
            return refuse("the strands' bytes ascend, each once");
        }
        if digits.iter().any(|(b, _)| keys.binary_search_by_key(b, |&(k, _)| k).is_ok()) {
            return refuse("a byte that is both a strands' digit and keyed");
        }
        if digits.iter().any(|(_, turns)| turns.len() != rings.len() || turns.iter().zip(&rings).any(|(&t, g)| t >= g.modulus)) {
            return refuse("a strands' digit turns each ring by a residue below its modulus");
        }
        if keys.iter().any(|(_, key)| key.source.iter().any(|v| !(-3..=3).contains(v))) {
            return refuse("a strands' key takes a strand or zero");
        }
        Ok(Self { level, rings, laws, digits, keys, words, levels: d.levels, alphabet: d.alphabet, modes: d.modes, half_turn: half_turn(2 * MOVE_BITS) })
    }

    /// The level whose contacts read them.
    pub fn level(&self) -> usize {
        self.level
    }

    /// The rings.
    pub fn rings(&self) -> &[StrandRing] {
        &self.rings
    }

    /// The three laws.
    pub fn laws(&self) -> [StrandLaw; 3] {
        self.laws
    }

    /// The located digit bytes and their turns.
    pub fn digits(&self) -> &[(u8, Vec<u32>)] {
        &self.digits
    }

    /// The located keyed bytes and their keys.
    pub fn keys(&self) -> &[(u8, StrandKey)] {
        &self.keys
    }

    /// The count of residues, `3R`: strand `s` on ring `i` at `s·R + i`.
    pub fn residues(&self) -> usize {
        3 * self.rings.len()
    }

    /// The count of the faces' parts the contacts read, `6R`: residue `j`'s face at `2j` (its real
    /// part) and `2j + 1` (its imaginary part).
    pub fn parts(&self) -> usize {
        6 * self.rings.len()
    }

    /// A stream's rested residues, strand-major, at zero.
    fn rested(&self) -> Vec<u32> {
        vec![0; self.residues()]
    }

    /// The residues (strand-major) and the orientation after the byte `b`, by the law above.
    pub fn hear_byte(&self, residues: &mut [u32], reversed: &mut bool, b: u8) {
        let n = self.rings.len();
        if let Ok(i) = self.digits.binary_search_by_key(&b, |(d, _)| *d) {
            let turns = &self.digits[i].1;
            for (s, law) in self.laws.iter().enumerate() {
                for (k, ring) in self.rings.iter().enumerate() {
                    residues[s * n + k] = law.at_digit(residues[s * n + k], turns[k], *ring, *reversed);
                }
            }
        } else if let Ok(i) = self.keys.binary_search_by_key(&b, |&(k, _)| k) {
            let key = self.keys[i].1;
            for (k, ring) in self.rings.iter().enumerate() {
                let moved = key.apply([residues[k], residues[n + k], residues[2 * n + k]], ring.modulus);
                for (s, v) in moved.into_iter().enumerate() {
                    residues[s * n + k] = v;
                }
            }
            *reversed = key.sheet.after(*reversed);
        }
    }

    /// The residues and the orientation after the word of `class` is heard, each byte in turn.
    pub fn heard(&self, residues: &mut [u32], reversed: &mut bool, class: usize) -> Result<()> {
        if residues.len() != self.residues() || class >= self.words.len() {
            return refuse("a stream rested before its strands joined: rest it again");
        }
        for &b in &self.words[class] {
            self.hear_byte(residues, reversed, b);
        }
        Ok(())
    }

    /// The faces `e^(2πi r/q)` of the residues, strand-major, as the parts the contacts read
    /// ([`Strands::parts`]) on the face's grain `2^(−16)`.
    pub fn faces(&self, residues: &[u32]) -> Result<Vec<i32>> {
        let n = self.rings.len();
        let mut parts = Vec::with_capacity(2 * residues.len());
        for (i, &v) in residues.iter().enumerate() {
            let (a, b) = ring_face_at(v, self.rings[i % n].modulus, self.half_turn);
            parts.push(fit32(release(a, MOVE_BITS - FACE_BITS), "a strand's face outgrew its carrier")?);
            parts.push(fit32(release(b, MOVE_BITS - FACE_BITS), "a strand's face outgrew its carrier")?);
        }
        Ok(parts)
    }

    /// `strands LEVELS ALPHABET MODES LEVEL LAW LAW LAW`, then the rings as `MODULUS:MULTIPLIER`,
    /// the digits as `BYTE:TURN,…`, the keys as `BYTE:S,S,S:SHEET` and the words in hexadecimal (`-`
    /// for an empty word), one line each.
    fn to_text(&self) -> String {
        let rings: String = self.rings.iter().map(|g| format!(" {}:{}", g.modulus, g.multiplier)).collect();
        let digits: String = self.digits.iter().map(|(b, turns)| format!(" {b}:{}", turns.iter().map(u32::to_string).collect::<Vec<_>>().join(","))).collect();
        let keys: String = self.keys.iter().map(|(b, key)| format!(" {b}:{}", key.text())).collect();
        let words: String = self.words.iter().map(|w| if w.is_empty() { " -".to_string() } else { format!(" {}", w.iter().map(|b| format!("{b:02x}")).collect::<String>()) }).collect();
        let [a, b, c] = self.laws.map(StrandLaw::name);
        format!(
            "strands {} {} {} {} {a} {b} {c}\nstrands-rings{rings}\nstrands-digits{digits}\nstrands-keys{keys}\nstrands-words{words}\n",
            self.levels, self.alphabet, self.modes, self.level
        )
    }

    fn from_text(head: &str, rings: &str, digits: &str, keys: &str, words: &str, declaration: &TowerDeclaration) -> Result<Self> {
        let d = declaration;
        let bad = TowerError::Refused("strands' text that is not the tower's");
        let head: Vec<&str> = head.split(' ').collect();
        if head.len() != 8 || head[..4].join(" ") != format!("strands {} {} {}", d.levels, d.alphabet, d.modes) {
            return Err(bad);
        }
        let count = |w: &str| w.parse::<usize>().map_err(|_| bad.clone());
        let law = |w: &str| StrandLaw::named(w).ok_or(bad.clone());
        // A tagged line's entries after its tag; a line with no entry holds none.
        let entries = |line: &'static str, text: &'_ str| -> Result<Vec<String>> {
            let rest = text.strip_prefix(line).ok_or(TowerError::Refused("strands' text that is not the tower's"))?;
            if rest.is_empty() {
                return Ok(Vec::new());
            }
            rest.strip_prefix(' ').map(|r| r.split(' ').map(str::to_string).collect()).ok_or(TowerError::Refused("strands' text that is not the tower's"))
        };
        let pair = |entry: &str| -> Result<(u8, String)> {
            let (b, v) = entry.split_once(':').ok_or(bad.clone())?;
            Ok((b.parse().map_err(|_| bad.clone())?, v.to_string()))
        };
        let rings = entries("strands-rings", rings)?
            .iter()
            .map(|e| {
                let (q, mu) = e.split_once(':').ok_or(bad.clone())?;
                Ok(StrandRing { modulus: q.parse().map_err(|_| bad.clone())?, multiplier: mu.parse().map_err(|_| bad.clone())? })
            })
            .collect::<Result<Vec<_>>>()?;
        let digits = entries("strands-digits", digits)?
            .iter()
            .map(|e| {
                let (b, turns) = pair(e)?;
                Ok((b, turns.split(',').map(|t| t.parse().map_err(|_| bad.clone())).collect::<Result<Vec<u32>>>()?))
            })
            .collect::<Result<Vec<_>>>()?;
        let keys = entries("strands-keys", keys)?
            .iter()
            .map(|e| {
                let (b, key) = pair(e)?;
                Ok((b, StrandKey::from_text(&key).ok_or(bad.clone())?))
            })
            .collect::<Result<Vec<_>>>()?;
        let words = entries("strands-words", words)?
            .iter()
            .map(|w| {
                if w == "-" {
                    return Ok(Vec::new());
                }
                if w.len() % 2 != 0 {
                    return Err(bad.clone());
                }
                (0..w.len()).step_by(2).map(|i| u8::from_str_radix(&w[i..i + 2], 16).map_err(|_| bad.clone())).collect()
            })
            .collect::<Result<Vec<Vec<u8>>>>()?;
        Self::new(d, count(head[4])?, rings, [law(head[5])?, law(head[6])?, law(head[7])?], digits, keys, words)
    }
}

/// `x` released by `s` bits, rounded half up, or widened by `−s` bits: a pair form's release.
fn shifted(x: i128, s: i32) -> Result<i128> {
    if s > 0 {
        Ok((x + (1i128 << (s - 1))) >> s)
    } else {
        x.checked_mul(1i128 << (-s)).ok_or(TowerError::Refused("a pair form's value outgrew its 128-bit carrier"))
    }
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
    /// The pair face's readout `V` (`A × k`) and its lift into the encoding `P` (`d × k`), empty
    /// families without a pair face.
    pair_readout: usize,
    pair_encoding: usize,
    /// The ring face's readout `W` (`A × (d + 1)·2R`) and its factors (`R` ranks of
    /// [`rank_material`]), empty families without a ring face.
    ring_readout: usize,
    ring_factors: usize,
    /// The strands' faces read at their level's contacts: `W_sa` (`f × 6R`) and, under a pair law,
    /// `W_sb` (`f × 6R`), empty families without strands ([`Strands`]).
    strand_contact: usize,
    strand_pair: usize,
    len: usize,
    /// `(start, length, the family's grain)`, in order.
    families: Vec<(usize, usize, u32)>,
}

impl Layout {
    fn new(d: &TowerDeclaration, forms: usize, ring_ranks: usize, ring_harmonics: usize, strand_parts: usize) -> Self {
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
        let (pair_readout, pair_encoding) = if forms > 0 { (take(a * forms, MATERIAL_BITS), take(w * forms, MATERIAL_BITS)) } else { (0, 0) };
        let (ring_readout, ring_factors) = if ring_ranks > 0 { (take(a * (w + 1) * 2 * ring_ranks * ring_harmonics, MATERIAL_BITS), take(ring_ranks * rank_material(d), MATERIAL_BITS)) } else { (0, 0) };
        let (strand_contact, strand_pair) = match strand_parts {
            0 => (0, 0),
            c if d.contact == ContactLaw::Rectifying => (take(f * c, MATERIAL_BITS), 0),
            c => (take(f * c, MATERIAL_BITS), take(f * c, MATERIAL_BITS)),
        };
        Self { encoding, levels, readout, readout_bias, pair_readout, pair_encoding, ring_readout, ring_factors, strand_contact, strand_pair, len: at, families }
    }
}

/// [definition; agent-inferred] **The located material**: every family as one vector of integer
/// numerators on its grain (`Layout`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower {
    pub declaration: TowerDeclaration,
    pub theta: Vec<i32>,
    /// The resident pair face, when one is joined ([`Tower::join_pair_face`]).
    pair: Option<PairFace>,
    /// The resident ring face, when one is joined ([`Tower::join_ring_face`]).
    ring: Option<RingFace>,
    /// The rotor, when one is joined ([`Tower::join_rotor`]).
    rotor: Option<Rotor>,
    /// The strands, when they are joined ([`Tower::join_strands`]).
    strands: Option<Strands>,
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
    /// The class that arrived last, the start `A` at rest: the pair face reads it beside the class
    /// arriving.
    pub previous: usize,
    /// Each level's passage credit, carried by a learner's streams (absent in a reading).
    pub credit: Option<Vec<LevelCredit>>,
    /// Each ring rank's carried value `r` on its push's grain (empty without a ring face).
    pub ring: Vec<(i128, i128)>,
    /// Each ring rank's hand ([`hand_after`]): `true` where the moves since its last restart
    /// reversed it, the ring then read as `(Re r, −Im r)`.
    pub hands: Vec<bool>,
    /// The strands' residues, strand-major (empty without strands, [`Strands`]).
    pub strands: Vec<u32>,
    /// The strands' orientation: `true` on the reversed sheet `o = −1`, `false` at rest.
    pub reversed: bool,
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
        face_code(self.masses[class], self.total)
    }

    /// The comparison's descent covector against `target`, `p̂ − [· = target]` on `2^(−24)`: the
    /// one law the reverse scan reads ([`covector`]), handed to an exterior reading.
    pub fn covector(&self, target: usize) -> Vec<i64> {
        covector(self, target)
    }

    /// The class's rank on the face: how many classes carry more mass than it (0 when none does).
    pub fn rank(&self, class: usize) -> usize {
        let m = self.masses[class];
        self.masses.iter().filter(|&&x| x > m).count()
    }
}

/// A class's code read off its mass and the face's total, `−log₂(mass/total)` on `2^(−20)` bits
/// ([`TowerFace::code`]).
pub fn face_code(mass: u128, total: u128) -> i64 {
    let p = (mass << UNIT_BITS) / total;
    -(log2_face(p.max(1), READ_BITS) as i64)
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

/// [agent-inferred, October 24] **One level's power at one cell** ([`Tower::read_circuit`]): the
/// modes' stored energy `Σ_k |h_k|²` before the class arrives (`before`), what the moves carry of it
/// (`carried`, `Σ_k |λ_t h_k + β_t h̄_k|²`, the memory after its loss) and the energy after the push
/// (`after`), all on the state's grain squared, `2^(−48)`. `before − carried ≥ 0` is what the level
/// dissipates at the tick (`|α_t| + |β_t| = ρ_t < 1`), and `after − carried` is the power the push
/// brings, negative where the push cancels what the modes carry. `scale` is the read's `‖r‖_rms`
/// and `drive` and `conduct` the contacts' largest drive and conduction, on `2^(−16)`. `modes`
/// holds the same reading mode by mode ([`CircuitMode`]), so an exterior reading can follow where
/// the flux goes: which modes lose, which the push enters, and whether it turns them or boosts them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitLevel {
    pub before: u128,
    pub carried: u128,
    pub after: u128,
    pub scale: i128,
    pub drive: u64,
    pub conduct: u64,
    pub modes: Vec<CircuitMode>,
}

/// [agent-inferred, October 24] **One mode at one cell** ([`Tower::read_circuit`]): its state
/// before the class arrives, what the step's moves carry of it (`λ_t h + β_t h̄`) and its state after
/// the push, on the state's grain `2^(−24)`, with the moves `λ_t` and `β_t` on `2^(−30)`. The
/// mode's loss is `|before|² − |carried|²`; the push `after − carried` splits against the carried
/// phase into a boost (its part along `carried`, `Re(conj(carried)·push)`) and a turn (its part
/// across, `Im(conj(carried)·push)`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitMode {
    pub before: (i64, i64),
    pub carried: (i64, i64),
    pub after: (i64, i64),
    pub lam: (i64, i64),
    pub beta: (i64, i64),
}

/// One cell of the circuit reading ([`Tower::read_circuit`]): each level's power, and the code of
/// the class that arrives next on `2^(−20)` bits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CircuitCell {
    pub levels: Vec<CircuitLevel>,
    pub code: i64,
}

/// [definition; agent-inferred, October 24] **What a cell's input receives**
/// ([`Tower::read_input_covectors`]): the class arriving, the state it meets (every level's modes
/// before the move, [`carried_face`]) and the covector the tower's own reverse sends to the cell's
/// input `x⁰` from every face after it in its section, on the encoding's covector grain `2^(−24)`.
/// The covector is the tension of the later faces carried back to where the class arrived: the
/// effective tension a lift of the input meets, which the encoding's own covector sums class by
/// class. `modes` is the covector the same reverse sends to every level's modes after the cell's
/// push, `G_h`, level by level and mode by mode `(re, im)`, on the covector's grain `2^(−24)`: the
/// tension of every later face carried back through each mode's own moves, which a value placed in
/// that mode at the cell meets (`δL = Re(conj(G_h) δh)`). `moves` is each mode's move at the cell,
/// `h ↦ λ_t h + β_t h̄`, level by level and mode by mode `(Re λ, Im λ, Re β, Im β)` on `2^(−30)`, as
/// [`Tower::read_circuit`] reads them: a carrier riding a mode's own moves is carried by them.
#[derive(Clone, Copy, Debug)]
pub struct InputCovector<'a> {
    pub class: usize,
    pub carried: &'a [i64],
    pub covector: &'a [i64],
    pub modes: &'a [i64],
    pub moves: &'a [i64],
}

/// The carried state as one face: level by level, each mode's `(re, im)` released from the
/// state's `2^(−24)` to the face's `2^(−16)`.
pub fn carried_face(modes: &[Vec<(i64, i64)>]) -> Result<Vec<i64>> {
    let mut face = Vec::with_capacity(2 * modes.iter().map(Vec::len).sum::<usize>());
    for &(re, im) in modes.iter().flatten() {
        face.push(fit64(release(re as i128, STATE_BITS - FACE_BITS))?);
        face.push(fit64(release(im as i128, STATE_BITS - FACE_BITS))?);
    }
    Ok(face)
}

/// `Σ_k |h_k|²` on the state's grain squared.
fn energy(modes: &[(i64, i64)]) -> Result<u128> {
    modes.iter().try_fold(0u128, |sum, &(re, im)| {
        let e = (re.unsigned_abs() as u128).pow(2).checked_add((im.unsigned_abs() as u128).pow(2));
        e.and_then(|e| sum.checked_add(e)).ok_or(TowerError::Refused("a level's energy outgrew its 128-bit carrier"))
    })
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
    /// The pair contact's second drive `W_b r̂ + W_sb s + b_b` (empty when rectifying).
    pair: Vec<i32>,
    conduct: Vec<i32>,
    /// The strands' faces `s` the contacts read beside `r̂`, on `2^(−16)` (empty off their level).
    strands: Vec<i32>,
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
    /// The pair face read at this cell (absent without one).
    pair: Option<Vec<i32>>,
    /// The ring face read at this cell, `ρ_t` on `2^(−16)` (absent without one).
    ring: Option<Vec<i32>>,
    /// Each rank's scale `‖q_t‖_rms`, the ratio's denominator.
    ring_scale: Option<Vec<i128>>,
    /// The ring's read before its ratio, each rank's `(Re, Im)` released by `read_shift`.
    ring_read: Option<Vec<i64>>,
    /// Each rank's ring after the cell, for the reverse.
    ring_after: Option<Vec<(i128, i128)>>,
    /// The ring's pair read with the top face, `φ = x̂ ⊗ ρ`, what its readout reads.
    ring_pair: Option<Vec<i32>>,
    /// The top face's ratio `x̂` (without its unit) and its scale, for the reverse.
    top_hat: Option<(Vec<i32>, i128)>,
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
    /// The pair face's readout `V` and lift `P` (zero without a pair face).
    pair: [u64; 2],
    /// The ring face's readout `W` (zero without a ring face).
    ring: u64,
    /// The strands' `W_sa` and `W_sb` (zero without strands).
    strands: [u64; 2],
    /// The ring's ranks as the material holds their factors, and each class's pool from them
    /// (empty without a ring face).
    ring_ranks: Vec<RingRank>,
    ring_pools: Vec<(i128, i128)>,
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

/// [agent-inferred, October 25] A rank's face `ρ` (two parts on `2^(−16)`) with its harmonics,
/// `q_1 = ρ` and `q_h = q_(h−1) ρ / |ρ|`, each rounded to the face's grain: `q_h = |ρ| e^(ihφ)`
/// ([`RingFace::with_harmonics`]). A face at zero carries zero harmonics.
fn harmonics_of(rho: &[i32], harmonics: usize) -> Result<Vec<i32>> {
    let (re, im) = (rho[0] as i128, rho[1] as i128);
    let modulus = ((re * re + im * im) as u128).isqrt() as i128;
    let mut q = Vec::with_capacity(2 * harmonics);
    q.extend_from_slice(&rho[..2]);
    let (mut x, mut y) = (re, im);
    for _ in 1..harmonics {
        if modulus == 0 {
            q.extend([0, 0]);
            continue;
        }
        (x, y) = (div_nearest(x * re - y * im, modulus), div_nearest(x * im + y * re, modulus));
        q.push(fit32(x, "a ring's harmonic outgrew its 32-bit carrier")?);
        q.push(fit32(y, "a ring's harmonic outgrew its 32-bit carrier")?);
    }
    Ok(q)
}

/// The adjoint of [`harmonics_of`] to the face `ρ`, on the face's tangent: with
/// `t = Σ_(h≥2) h (∂q_h,im q_h,re − ∂q_h,re q_h,im)` the covector on the turn `φ`,
/// `∂ρ = ∂q_1 + t (−ρ_im, ρ_re) / |ρ|²`. The harmonics' radial part is dropped: `ρ` is a ratio to
/// its own power, whose adjoint ([`ratio_adjoint`]) returns no radial covector.
fn harmonics_adjoint(face: &[i32], cov: &[i64]) -> Result<[i64; 2]> {
    let (re, im) = (face[0] as i128, face[1] as i128);
    let n2 = re * re + im * im;
    let mut d = [cov[0], cov[1]];
    if n2 == 0 || face.len() <= 2 {
        return Ok(d);
    }
    let wide = || TowerError::Refused("a ring's harmonic covector outgrew its 128-bit carrier");
    let mut t = 0i128;
    for (h, (q, g)) in face.chunks_exact(2).zip(cov.chunks_exact(2)).enumerate().skip(1) {
        let turn = (g[1] as i128 * q[0] as i128).checked_sub(g[0] as i128 * q[1] as i128).and_then(|v| v.checked_mul(h as i128 + 1)).ok_or_else(wide)?;
        t = t.checked_add(turn).ok_or_else(wide)?;
    }
    d[0] = fit64(d[0] as i128 + div_nearest(t.checked_mul(-im).ok_or_else(wide)?, n2))?;
    d[1] = fit64(d[1] as i128 + div_nearest(t.checked_mul(re).ok_or_else(wide)?, n2))?;
    Ok(d)
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
    /// tower opens on the flat face (birth at zero) and each level on the identity. The turn ladder
    /// is [`TurnLadder::Fixed`]; [`Tower::found_on`] founds on a declared one.
    pub fn found(declaration: TowerDeclaration, keys: &[u8]) -> Result<Self> {
        Self::found_on(declaration, keys, TurnLadder::Fixed)
    }

    /// The founding of [`Tower::found`] on a declared [`TurnLadder`]. The keys are drawn in the
    /// same order whatever the ladder, so two ladders founded on one key stream share their
    /// encoding, pushes, reads and contacts and differ only in their modes' turns.
    pub fn found_on(declaration: TowerDeclaration, keys: &[u8], ladder: TurnLadder) -> Result<Self> {
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
        let layout = Layout::new(&d, 0, 0, 0, 0);
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
        if ladder == TurnLadder::Both && d.modes % 2 != 0 {
            return refuse("two turn ladders need an even bank");
        }
        // The modes one ladder spans: the bank, or each half of it.
        let span = if ladder == TurnLadder::Both { d.modes / 2 } else { d.modes };
        let turns = turn_ladder(span);
        let sqrt_width = (d.width as u128).isqrt().max(1);
        for lv in &layout.levels {
            for k in 0..d.modes {
                let (place, scaled) = match ladder {
                    TurnLadder::Fixed => (k, false),
                    TurnLadder::Scaled => (k, true),
                    TurnLadder::Both => (k % span, k >= span),
                };
                let s = (place / turns) as u32 + 1;
                let j = (place % turns) as u64;
                let rho = (1i128 << MOVE_BITS) - (1i128 << (MOVE_BITS - s.min(MARGIN)));
                // The turn by j·π/turns, or by j·π/(turns·2^(s−1)) on rung s when scaled (the
                // margin's rung past it): turns is a power of two by the ladder's declaration, so
                // the turn is dyadic.
                let n = turns.trailing_zeros() + if scaled { s.min(MARGIN) - 1 } else { 0 };
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
        Ok(Self { declaration: d, theta, pair: None, ring: None, rotor: None, strands: None, layout, exponential: Exponential::new(FACE_BITS), fine: Exponential::new(MOVE_BITS) })
    }

    /// The rested state: every mode at zero, at the start.
    pub fn rest(&self) -> TowerState {
        TowerState {
            modes: vec![vec![(0, 0); self.declaration.modes]; self.declaration.levels],
            previous: self.declaration.alphabet,
            credit: None,
            ring: vec![(0, 0); self.ring.as_ref().map_or(0, RingFace::ranks)],
            hands: vec![false; self.ring.as_ref().map_or(0, RingFace::ranks)],
            strands: self.strands.as_ref().map_or_else(Vec::new, Strands::rested),
            reversed: false,
        }
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
        let pair = match &self.pair {
            Some(face) => {
                let (k, l) = (face.forms(), &self.layout);
                [reach(&t[l.pair_readout..l.pair_readout + d.alphabet * k]), reach(&t[l.pair_encoding..l.pair_encoding + d.width * k])]
            }
            None => [0, 0],
        };
        let ring = self.ring.as_ref().map_or(0, |face| {
            let rr = self.layout.ring_readout;
            reach(&t[rr..rr + d.alphabet * face.channels(d.width)])
        });
        let (ring_ranks, ring_pools) = match &self.ring {
            Some(face) => {
                let rf = self.layout.ring_factors;
                let ranks = face.ranks_of(d, &t[rf..rf + face.ranks() * rank_material(d)]);
                let pools = face.pools_of(d.width, &ranks);
                (ranks, pools)
            }
            None => (Vec::new(), Vec::new()),
        };
        let strands = self.strands.as_ref().map_or([0, 0], |strands| {
            let (l, extent) = (&self.layout, d.contacts * strands.parts());
            let pair = if d.contact == ContactLaw::Rectifying { 0 } else { reach(&t[l.strand_pair..l.strand_pair + extent]) };
            [reach(&t[l.strand_contact..l.strand_contact + extent]), pair]
        });
        Reaches { levels, readout: reach(&t[self.layout.readout..self.layout.readout + d.alphabet * d.width]), pair, ring, strands, ring_ranks, ring_pools, gammas, gates, ladder, half_turn }
    }

    /// One cell forward: the class `u` arrives, every level's modes move, and the face of the next
    /// class is read. The temporaries are returned for the reverse scan.
    fn step(&self, state: &mut TowerState, u: usize, reaches: &Reaches) -> Result<Cell> {
        let d = &self.declaration;
        let (w, n, f) = (d.width, d.modes, d.contacts);
        if u >= d.alphabet {
            return refuse("a class outside the declared alphabet");
        }
        if state.previous > d.alphabet {
            return refuse("a carried class outside the declared alphabet and its start");
        }
        let t = &self.theta;
        let e = self.layout.encoding + u * w;
        let mut x: Vec<i32> = t[e..e + w].to_vec();
        // The pair face read at (the class before, the class arriving), lifted into the encoding:
        // `x⁰ = E(u) + P c(p)`, on 2^(−40) released to the face's 2^(−16).
        let pair = self.pair.as_ref().map(|face| face.at(state.previous, u));
        let seam = state.previous;
        state.previous = u;
        if let Some(c) = pair {
            let k = c.len();
            let pe = self.layout.pair_encoding;
            let mut lift = vec![0i64; w];
            affine(&t[pe..pe + w * k], reaches.pair[1], k, c, None, 0, MATERIAL_BITS, &mut lift)?;
            x = collect_exact(x.iter().zip(&lift).map(|(a, b)| fit32(*a as i128 + *b as i128, "the pair face's lift outgrew the face's 32-bit carrier")))?;
        }
        // The strands hear the arriving word; their faces are read at their level's contacts
        // beside the level's read ([`Strands`]).
        let stranded: Option<(usize, Vec<i32>)> = match &self.strands {
            Some(strands) => {
                strands.heard(&mut state.strands, &mut state.reversed, u)?;
                Some((strands.level, strands.faces(&state.strands)?))
            }
            None => None,
        };
        let mut levels = Vec::with_capacity(d.levels);
        let mut ring_read: Option<Vec<i64>> = None;
        let mut ring_face: Option<Vec<i32>> = None;
        let mut ring_scale: Option<Vec<i128>> = None;
        let mut ring_after: Option<Vec<(i128, i128)>> = None;
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
            // The ring's carried face before the move, in [`carried_face`]'s order.
            let ring_face_before: Option<Vec<i64>> = match &self.ring {
                Some(face) if face.level == l => Some(carried_face(std::slice::from_ref(&state.modes[l]))?),
                _ => None,
            };
            // The rotor's step and turn `h' = T P^σ h` before the move ([`Rotor`]).
            let stepped: Option<Vec<(i64, i64)>> = self.rotor.as_ref().filter(|r| !r.still(l, u)).map(|r| r.moved(l, u, &state.modes[l])).transpose()?;
            let modes = &mut state.modes[l];
            let gammas = &reaches.gammas[l];
            let mut face = vec![0i64; 2 * n];
            for k in 0..n {
                let (hr, hi) = stepped.as_ref().map_or(modes[k], |h| h[k]);
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
            // The strands' faces read at this level's contacts beside `r̂`: `W_s s`, each drive's
            // part released on its own as the pair face's lift is.
            let faces = stranded.as_ref().filter(|(level, _)| *level == l).map(|(_, s)| s.as_slice());
            let heard = |material: usize, reach: u64, drive: &mut [i64]| -> Result<()> {
                let Some(s) = faces else { return Ok(()) };
                let c = s.len();
                let mut part = vec![0i64; f];
                affine(&t[material..material + f * c], reach, c, s, None, 0, MATERIAL_BITS, &mut part)?;
                for (a, b) in drive.iter_mut().zip(&part) {
                    *a = fit64(*a as i128 + *b as i128)?;
                }
                Ok(())
            };
            let drive_buf = &mut buf[..f];
            affine(&t[lv.contact..lv.contact + f * w], r[4], w, &read, Some(&t[lv.contact_bias..lv.contact_bias + f]), MATERIAL_BITS, MATERIAL_BITS, drive_buf)?;
            heard(self.layout.strand_contact, reaches.strands[0], drive_buf)?;
            let drive = to32(drive_buf, "a contact drive outgrew its 32-bit carrier")?;
            let (conduct, pair) = match d.contact {
                ContactLaw::Rectifying => (drive.iter().map(|&a| a.max(0)).collect(), Vec::new()),
                law => {
                    // The second drive W_b r̂ + b_b, and v = a ⊙ b on 2^(−32) released to the face
                    // (the foil: a b_b + b_a (b − b_b), the product's block held at zero).
                    let mut second = vec![0i64; f];
                    affine(&t[lv.pair..lv.pair + f * w], r[10], w, &read, Some(&t[lv.pair_bias..lv.pair_bias + f]), MATERIAL_BITS, MATERIAL_BITS, &mut second)?;
                    heard(self.layout.strand_pair, reaches.strands[1], &mut second)?;
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
            // The ring rides its mode's move at this cell (its founded pair move where it has one),
            // pushed from the face it carried before.
            if let (Some(face), Some(s)) = (&self.ring, &ring_face_before) {
                let m = face.mode;
                let (lam, beta) = match gate.get(m) {
                    Some(g) => ((g.lam.0 as i128, g.lam.1 as i128), (g.beta.0 as i128, g.beta.1 as i128)),
                    None => ((t[lv.move_re + m] as i128, t[lv.move_im + m] as i128), (0, 0)),
                };
                let read = RingFace::advance(&reaches.ring_ranks, &reaches.ring_pools, &face.restarts, &mut state.ring, &mut state.hands, s, u, &face.moves_at(seam, u, [lam.0, lam.1, beta.0, beta.1]))?;
                let (rho, scales) = face.face(&read)?;
                ring_face = Some(rho);
                ring_scale = Some(scales);
                ring_read = Some(read);
                ring_after = Some(state.ring.clone());
            }
            let push = push_re.into_iter().zip(push_im).collect();
            let strands = faces.map_or_else(Vec::new, <[i32]>::to_vec);
            levels.push(LevelCell { input: std::mem::replace(&mut x, next), push, state: state_copy, state_face: face, read, read_scale, drive, pair, conduct, gate, strands });
        }
        let a = d.alphabet;
        let mut z = vec![0i64; a];
        let ro = self.layout.readout;
        let rb = self.layout.readout_bias;
        affine(&t[ro..ro + a * w], reaches.readout, w, &x, Some(&t[rb..rb + a]), MATERIAL_BITS, MATERIAL_BITS, &mut z)?;
        // The pair face read by its own readout: `z += V c(p)`, released to 2^(−16) beside the
        // tower's read.
        if let Some(c) = pair {
            let k = c.len();
            let pr = self.layout.pair_readout;
            let mut read = vec![0i64; a];
            affine(&t[pr..pr + a * k], reaches.pair[0], k, c, None, 0, MATERIAL_BITS, &mut read)?;
            for (zv, r) in z.iter_mut().zip(&read) {
                *zv = fit64(*zv as i128 + *r as i128)?;
            }
        }
        // The ring read through its pair contact with the top face: `z += W (x̂ ⊗ ρ)`, released
        // to 2^(−16).
        let (mut ring_pair, mut top_hat) = (None, None);
        if let Some(rho) = &ring_face {
            let (phi, hat, scale) = RingFace::pair_read(&x, rho)?;
            let k = phi.len();
            let rr = self.layout.ring_readout;
            let mut read = vec![0i64; a];
            affine(&t[rr..rr + a * k], reaches.ring, k, &phi, None, 0, MATERIAL_BITS, &mut read)?;
            for (zv, r) in z.iter_mut().zip(&read) {
                *zv = fit64(*zv as i128 + *r as i128)?;
            }
            ring_pair = Some(phi);
            top_hat = Some((hat, scale));
        }
        let zmax = *z.iter().max().expect("a nonempty alphabet");
        let masses: Vec<u128> = z.iter().map(|&v| self.exponential.below_one((v - zmax) as i128)).collect();
        let total = masses.iter().sum();
        Ok(Cell { levels, top: x, pair: pair.map(|c| c.to_vec()), ring: ring_face, ring_scale, ring_read, ring_after, ring_pair, top_hat, face: TowerFace { masses, total } })
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
        self.reverse_joined(opening, cells, classes, None, compared, None).map(|(g, _)| g)
    }

    /// The reverse scan with a covector reaching each cell's top from outside the tower (the
    /// duplex's meeting, `duplex`), on the top covector's grain `2^(−24)`, added to the one the
    /// tower's own face sends there. `compared` declares, place by place, the class each face is
    /// compared with (the class that arrived when it is `None`): a place with no comparison is the
    /// tower's own release re-entering what it reads, which brings no news, so its face sends no
    /// covector, while the covectors of the places after it still return through the state it
    /// moved; a place compared with another class than the one read there is the tower's own
    /// release read against the truth where the two part. Beside the families' covector it returns
    /// each cell's input covector `δx⁰` (what the encoding's covector sums), on `2^(−24)`, and, when
    /// `modes` is given, keeps there every level's mode covectors `G_h` cell by cell
    /// (`modes[level][cell][mode]`, the covector of the modes after the cell's push).
    #[allow(clippy::too_many_arguments)]
    fn reverse_joined(
        &self,
        opening: &TowerState,
        cells: &[Cell],
        classes: &[usize],
        joined: Option<&[Vec<i64>]>,
        compared: Option<&[Option<usize>]>,
        mut modes: Option<&mut Vec<Vec<Vec<(i64, i64)>>>>,
    ) -> Result<(Vec<i128>, Vec<Vec<i64>>)> {
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
        if let Some(out) = modes.as_deref_mut() {
            *out = vec![Vec::new(); d.levels];
        }
        if compared.is_some_and(|m| m.len() != classes.len()) {
            return refuse("a comparison for each class of the section");
        }
        if self.rotor.is_some() && opening.credit.is_some() {
            return refuse("a credited opening under a rotor: the credit's moments through the step are owed");
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
        // The pair face's readout takes the face's covector against the pair read there.
        let pairs: Vec<&[i32]> = cells.iter().filter_map(|cell| cell.pair.as_deref()).collect();
        let forms = self.pair.as_ref().map_or(0, |face| face.forms());
        if forms > 0 {
            if pairs.len() != cells_n {
                return refuse("a pair read at every cell of a pair-faced tower");
            }
            let pr = self.layout.pair_readout;
            outer_sum(&mut g[pr..pr + a * forms], forms, &dzs, &pairs)?;
        }
        // The ring's pair contact with the top face takes the face's covector against `x̂ ⊗ ρ`.
        // Its covector returns to the top through `x̂`'s ratio, and to each rank's read through
        // `ρ`'s, which is carried to the ring at its level and to the factors that pushed it.
        let mut ring_cov: Vec<Vec<i64>> = Vec::new();
        if let Some(face) = &self.ring {
            let (r2, h2) = (2 * face.ranks() * face.harmonics(), 2 * face.harmonics());
            let (k, rr) = (face.channels(w), self.layout.ring_readout);
            let reads: Vec<&[i32]> = cells.iter().filter_map(|cell| cell.ring_pair.as_deref()).collect();
            if reads.len() != cells_n {
                return refuse("a ring read at every cell of a ring-faced tower");
            }
            outer_sum(&mut g[rr..rr + a * k], k, &dzs, &reads)?;
            ring_cov.reserve(cells_n);
            for (top, (dz, cell)) in dx.iter_mut().zip(dzs.iter().zip(cells)) {
                let mut back = vec![0i64; k];
                transposed(&t[rr..rr + a * k], reaches.ring, k, dz, MATERIAL_BITS, &mut back)?;
                let missing = || TowerError::Refused("a ring read at every cell of a ring-faced tower");
                let (rho, scales) = cell.ring.as_deref().zip(cell.ring_scale.as_deref()).ok_or_else(missing)?;
                let (hat, top_scale) = cell.top_hat.as_ref().ok_or_else(missing)?;
                // ∂ρ_k = Σ_j ∂φ_jk x̂_j and ∂x̂_j = Σ_k ∂φ_jk ρ_k, each released by the face's grain.
                let mut d_rho = vec![0i128; r2];
                let mut d_hat = Vec::with_capacity(w);
                for (j, row) in back.chunks_exact(r2).enumerate() {
                    let xj = hat.get(j).map_or(1i128 << FACE_BITS, |&v| v as i128);
                    for (slot, &b) in d_rho.iter_mut().zip(row) {
                        *slot += b as i128 * xj;
                    }
                    if j < w {
                        d_hat.push(fit64(release(row.iter().zip(rho).map(|(&b, &r)| b as i128 * r as i128).sum(), FACE_BITS))?);
                    }
                }
                let d_rho: Vec<i64> = collect_exact(d_rho.into_iter().map(|v| fit64(release(v, FACE_BITS))))?;
                let mut read = Vec::with_capacity(2 * face.ranks());
                for (r, &scale) in scales.iter().enumerate() {
                    let (q, dq) = (&rho[h2 * r..h2 * (r + 1)], &d_rho[h2 * r..h2 * (r + 1)]);
                    read.extend(ratio_adjoint(&q[..2], scale, &harmonics_adjoint(q, dq)?)?);
                }
                ring_cov.push(read);
                for (v, e) in top.iter_mut().zip(ratio_adjoint(hat, *top_scale, &d_hat)?) {
                    *v = fit64(*v as i128 + e as i128)?;
                }
            }
        }
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
            // The ring rides this level: its face's covector reaches the carried face each push read
            // (the state after the cell before, on the modes' convention) and the mode's move.
            let mut ring_moves: Vec<[i128; 4]> = Vec::new();
            let mut ring_mode = usize::MAX;
            if let Some(face) = self.ring.as_ref().filter(|face| face.level == l) {
                if opening.credit.is_some() {
                    return refuse("a credited opening under a ring face: the opening state's covector through the ring is owed");
                }
                let m = face.mode;
                let faces: Vec<Vec<i64>> = collect_exact((0..cells_n).map(|i| carried_face(std::slice::from_ref(if i == 0 { &opening.modes[l] } else { &cells[i - 1].levels[l].state }))))?;
                let seams: Vec<usize> = (0..cells_n).map(|i| if i == 0 { opening.previous } else { classes[i - 1] }).collect();
                let mode_moves: Vec<[i128; 4]> = cells
                    .iter()
                    .map(|cell| match cell.levels[l].gate.get(m) {
                        Some(gm) => [gm.lam.0 as i128, gm.lam.1 as i128, gm.beta.0 as i128, gm.beta.1 as i128],
                        None => [t[lv.move_re + m] as i128, t[lv.move_im + m] as i128, 0, 0],
                    })
                    .collect();
                let moves: Vec<Vec<[i128; 4]>> = (0..cells_n).map(|i| face.moves_at(seams[i], classes[i], mode_moves[i])).collect();
                let after: Vec<&[(i128, i128)]> = cells.iter().filter_map(|cell| cell.ring_after.as_deref()).collect();
                if after.len() != cells_n || opening.ring.len() != face.ranks() || opening.hands.len() != face.ranks() {
                    return refuse("a ring carried at every cell of a ring-faced tower");
                }
                let (d_face, d_moves, d_factors) = face.reverse(&reaches.ring_ranks, &reaches.ring_pools, &opening.ring, &opening.hands, &after, &faces, &classes[..cells_n], &moves, &ring_cov)?;
                let rf = self.layout.ring_factors;
                for (slot, v) in g[rf..rf + d_factors.len()].iter_mut().zip(d_factors) {
                    *slot += v;
                }
                // ŝ_t is the state after cell t − 1; the opening's state is not material.
                for i in 1..cells_n {
                    for (j, slot) in read_cov[i - 1].iter_mut().enumerate() {
                        *slot = (fit64(slot.0 as i128 + d_face[i][2 * j] as i128)?, fit64(slot.1 as i128 + d_face[i][2 * j + 1] as i128)?);
                    }
                }
                // Where a rank rode a founded pair move, the mode carried no ring of it: its covector
                // of that move stays with the held pair move. The mode's move takes the rest.
                let k = face.ranks();
                ring_moves = (0..cells_n)
                    .map(|i| {
                        let mut dm = [0i128; 4];
                        for r in (0..k).filter(|&r| face.pair_move(r, seams[i], classes[i]).is_none()) {
                            for (slot, v) in dm.iter_mut().zip(d_moves[i * k + r]) {
                                *slot += v;
                            }
                        }
                        dm
                    })
                    .collect();
                ring_mode = m;
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
            // The strands' faces read at this level: their material takes each drive's covector
            // against the faces, and the faces carry none.
            if let Some(strands) = self.strands.as_ref().filter(|strands| strands.level == l) {
                let c = strands.parts();
                let faces: Vec<&[i32]> = (0..cells_n).map(|i| level(i).strands.as_slice()).collect();
                let sc = self.layout.strand_contact;
                outer_sum(&mut g[sc..sc + f * c], c, &das, &faces)?;
                if d.contact != ContactLaw::Rectifying {
                    let sp = self.layout.strand_pair;
                    outer_sum(&mut g[sp..sp + f * c], c, &dbs, &faces)?;
                }
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
                // conj(λ_(t+1)) G_h(t+1) (+ β_(t+1) conj(G_h(t+1))): the covector of h'_t.
                let mut back: Vec<(i128, i128)> = (0..n)
                    .map(|k| {
                        let (lr, li) = match later {
                            Some(gate) => (gate[k].lam.0 as i128, gate[k].lam.1 as i128),
                            None => (t[lv.move_re + k] as i128, t[lv.move_im + k] as i128),
                        };
                        let (br, bi) = later.map_or((0, 0), |gate| (gate[k].beta.0 as i128, gate[k].beta.1 as i128));
                        let (cr, ci) = (carried[k].0 as i128, carried[k].1 as i128);
                        (release(lr * cr + li * ci + br * cr + bi * ci, MOVE_BITS), release(lr * ci - li * cr + bi * cr - br * ci, MOVE_BITS))
                    })
                    .collect();
                // The rotor's step and turn carried back by the monomial's adjoint: mode k of h'_t
                // took mode source(k) of h_t turned by its key, so its covector returns there turned
                // back ([`Rotor`]).
                if let Some(rotor) = self.rotor.as_ref().filter(|r| i + 1 < cells_n && !r.still(l, classes[i + 1])) {
                    back = rotor.back(l, classes[i + 1], &back);
                }
                for k in 0..n {
                    gh.push((fit64(read_cov[i][k].0 as i128 + back[k].0)?, fit64(read_cov[i][k].1 as i128 + back[k].1)?));
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
                let unstepped: &[(i64, i64)] = if i == 0 { &opening.modes[l] } else { &cells[i - 1].levels[l].state };
                // The covectors of the move read the state it acted on, h' = T P^σ h ([`Rotor`]).
                let stepped = self.rotor.as_ref().filter(|r| !r.still(l, classes[i])).map(|r| r.moved(l, classes[i], unstepped)).transpose()?;
                let previous: &[(i64, i64)] = stepped.as_deref().unwrap_or(unstepped);
                let gh = &gh_all[i];
                let mut dq = vec![0i64; if d.gated { n } else { 0 }];
                let mut ds = vec![0i64; if d.turned { n } else { 0 }];
                let mut dk = vec![0i64; if d.pumped { n } else { 0 }];
                let mut dp = vec![0i64; if d.pumped { n } else { 0 }];
                for k in 0..n {
                    let (hr, hi) = (previous[k].0 as i128, previous[k].1 as i128);
                    let (gr, gi) = (gh[k].0 as i128, gh[k].1 as i128);
                    // conj(h_(t−1)) G_h(t), the covector of λ_t, and Re(conj(G_h) B x), of γ_t.
                    // The ring's covector of the move it rode, on the same convention.
                    let ring_move = if k == ring_mode { ring_moves[i] } else { [0; 4] };
                    let (glr, gli) = (hr * gr + hi * gi + ring_move[0], hr * gi - hi * gr + ring_move[1]);
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
                            let (gbr, gbi) = (hr * gr - hi * gi + ring_move[2], hr * gi + hi * gr + ring_move[3]);
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
            if let Some(out) = modes.as_deref_mut() {
                out[l] = std::mem::take(&mut gh_all);
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
        // The lift takes the bottom face's covector against the pair: `G_P = Σ δx⁰ c(p)ᵀ`.
        if forms > 0 {
            let pe = self.layout.pair_encoding;
            outer_sum(&mut g[pe..pe + w * forms], forms, &dx, &pairs)?;
        }
        Ok((g, dx))
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
        if self.rotor.is_some() {
            return refuse("a passage credit under a rotor: its moments through the step are owed");
        }
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
                *v = on_step_grain(grain, *v);
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
        if let Some(face) = &self.pair {
            s.push_str(&face.to_text());
        }
        if let Some(face) = &self.ring {
            s.push_str(&face.to_text());
        }
        if let Some(rotor) = &self.rotor {
            s.push_str(&rotor.to_text());
        }
        if let Some(strands) = &self.strands {
            s.push_str(&strands.to_text());
        }
        s
    }

    /// The count of lines [`Tower::to_text`] takes for the tower whose text begins `text`: two,
    /// three more with a pair face, two more with a ring face (one more a rank with its pair
    /// moves, one more with its harmonics and one more with its restarts), three more with a
    /// rotor and five more with strands.
    fn text_lines(text: &str) -> usize {
        let mut n = 2;
        if text.lines().nth(n).is_some_and(|l| l.starts_with("pair-face ")) {
            n += 3;
        }
        if text.lines().nth(n).is_some_and(|l| l.starts_with("ring-face ")) {
            n += 2;
            while text.lines().nth(n).is_some_and(|l| l.starts_with("ring-moves ")) {
                n += 1;
            }
            if text.lines().nth(n).is_some_and(|l| l.starts_with("ring-harmonics ")) {
                n += 1;
            }
            if text.lines().nth(n).is_some_and(|l| l.starts_with("ring-restarts ")) {
                n += 1;
            }
        }
        if text.lines().nth(n).is_some_and(|l| l.starts_with("rotor ")) {
            n += 3;
        }
        if text.lines().nth(n).is_some_and(|l| l.starts_with("strands ")) {
            n += 5;
        }
        n
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
        let theta: Vec<i32> = lines
            .next()
            .unwrap_or("")
            .split(' ')
            .map(|s| s.parse::<i32>().map_err(|_| TowerError::Refused("material that is not an integer")))
            .collect::<Result<_>>()?;
        let mut lines = lines.peekable();
        let pair = match lines.next_if(|l| l.starts_with("pair-face ")) {
            Some(head) => {
                let (forms, opening) = (lines.next().unwrap_or(""), lines.next().unwrap_or(""));
                Some(PairFace::from_text(head, forms, opening, declaration.alphabet, declaration.width)?)
            }
            None => None,
        };
        let ring = match lines.next_if(|l| l.starts_with("ring-face ")) {
            Some(head) => {
                let opening = lines.next().unwrap_or("");
                let mut moves = Vec::new();
                while let Some(line) = lines.next_if(|l| l.starts_with("ring-moves ")) {
                    moves.push(line);
                }
                let harmonics = lines.next_if(|l| l.starts_with("ring-harmonics "));
                let restarts = lines.next_if(|l| l.starts_with("ring-restarts "));
                Some(RingFace::from_text(head, opening, &moves, harmonics, restarts, &declaration)?)
            }
            None => None,
        };
        let rotor = match lines.next_if(|l| l.starts_with("rotor ")) {
            Some(head) => {
                let (steps, turns) = (lines.next().unwrap_or(""), lines.next().unwrap_or(""));
                Some(Rotor::from_text(head, steps, turns, &declaration)?)
            }
            None => None,
        };
        let strands = match lines.next_if(|l| l.starts_with("strands ")) {
            Some(head) => {
                let (rings, digits, keys, words) = (lines.next().unwrap_or(""), lines.next().unwrap_or(""), lines.next().unwrap_or(""), lines.next().unwrap_or(""));
                Some(Strands::from_text(head, rings, digits, keys, words, &declaration)?)
            }
            None => None,
        };
        let layout = Layout::new(
            &declaration,
            pair.as_ref().map_or(0, |face| face.forms()),
            ring.as_ref().map_or(0, RingFace::ranks),
            ring.as_ref().map_or(0, RingFace::harmonics),
            strands.as_ref().map_or(0, Strands::parts),
        );
        if theta.len() != layout.len || lines.next().is_some() {
            return refuse("material of the wrong extent");
        }
        // The rotor and the strands join by their own laws, so a text that holds them together is
        // read under the same refusals as their joins; the strands' material is the text's.
        let mut tower = Self { declaration, theta, pair, ring, rotor: None, strands: None, layout, exponential: Exponential::new(FACE_BITS), fine: Exponential::new(MOVE_BITS) };
        if let Some(rotor) = rotor {
            tower.join_rotor(rotor)?;
        }
        if let Some(strands) = strands {
            let theta = std::mem::take(&mut tower.theta);
            tower.join_strands(strands)?;
            tower.theta = theta;
        }
        Ok(tower)
    }

    /// [agent-inferred, October 24] **The pair face joined to the tower**: the face's readout `V`
    /// and lift `P` are appended to the material at zero, so the joined tower reads every passage
    /// exactly as the tower did, and the section's covector moves them from there. Refused when a
    /// face is already joined or the face's alphabet or width is not the tower's.
    pub fn join_pair_face(&mut self, face: PairFace) -> Result<()> {
        let d = &self.declaration;
        if self.pair.is_some() {
            return refuse("a tower takes one pair face");
        }
        if self.ring.is_some() {
            return refuse("a pair face joins before a ring face (the ring's readout follows the pair's material)");
        }
        if self.strands.is_some() {
            return refuse("a pair face joins before strands (the strands' material follows the pair's)");
        }
        if face.alphabet != d.alphabet || face.opening.len() != d.alphabet * d.width {
            return refuse("a pair face founded on another alphabet or width");
        }
        let layout = Layout::new(d, face.forms(), 0, 0, 0);
        self.theta.resize(layout.len, 0);
        self.layout = layout;
        self.pair = Some(face);
        Ok(())
    }

    /// The resident pair face, when one is joined.
    pub fn pair_face(&self) -> Option<&PairFace> {
        self.pair.as_ref()
    }

    /// [agent-inferred, October 25] **The ring face joined to the tower**: its readout `W` is
    /// appended to the material at zero, so the joined tower reads every passage exactly as the
    /// tower did (the ring is carried, and read with no weight), and its founded factors after it
    /// on the material's grain ([`factor_on_material`]); its founding opens `W` on the passage
    /// ([`Tower::open_ring_readout`]) and the section's covector moves both from there. A stream
    /// rested before the join carries no ring: rest it again. Refused when a ring face is already
    /// joined or comes without its founded factors.
    pub fn join_ring_face(&mut self, face: RingFace) -> Result<()> {
        if self.ring.is_some() {
            return refuse("a tower takes one ring face");
        }
        if self.rotor.is_some() {
            return refuse("a ring face beside a rotor: the ring's law under a step is owed");
        }
        if self.strands.is_some() {
            return refuse("a ring face joins before strands (the strands' material follows the ring's)");
        }
        let mut face = face;
        let layout = Layout::new(&self.declaration, self.pair.as_ref().map_or(0, PairFace::forms), face.ranks(), face.harmonics(), 0);
        if face.founded.len() != face.ranks() * rank_material(&self.declaration) {
            return refuse("a ring face joins with its founded factors");
        }
        if face.restarts.iter().flatten().any(|&c| c >= self.declaration.alphabet) {
            return refuse("a ring's restarting class arrives from the alphabet");
        }
        self.theta.resize(layout.len, 0);
        let rf = layout.ring_factors;
        self.theta[rf..rf + face.founded.len()].copy_from_slice(&face.founded);
        face.founded = Vec::new();
        self.layout = layout;
        self.ring = Some(face);
        Ok(())
    }

    /// The resident ring face, when one is joined.
    pub fn ring_face(&self) -> Option<&RingFace> {
        self.ring.as_ref()
    }

    /// [agent-inferred with the mathematics thread, October 26] **The rotor joined to the tower**
    /// ([`Rotor`]): it adds no material and no state, so a rotor that steps and turns nothing
    /// leaves every passage read as before, and a located one changes only the state each move acts
    /// on.
    /// Refused beside a ring face (a ring founded on a mode's own moves reads the mode unstepped;
    /// its law under a step is owed) or when one is already joined.
    pub fn join_rotor(&mut self, rotor: Rotor) -> Result<()> {
        if self.rotor.is_some() {
            return refuse("a tower takes one rotor");
        }
        if self.ring.is_some() {
            return refuse("a rotor beside a ring face: the ring's law under a step is owed");
        }
        let d = &self.declaration;
        if (rotor.levels, rotor.alphabet, rotor.modes) != (d.levels, d.alphabet, d.modes) {
            return refuse("a rotor of another tower's shape");
        }
        self.rotor = Some(rotor);
        Ok(())
    }

    /// The rotor, when one is joined.
    pub fn rotor(&self) -> Option<&Rotor> {
        self.rotor.as_ref()
    }

    /// [agent-inferred, October 27] **The strands joined to the tower** ([`Strands`]): their faces'
    /// material at their level's contacts, `W_sa` and under a pair law `W_sb`, is appended at zero,
    /// so the joined tower reads every passage exactly as the tower did, and the section's covector
    /// moves it from there. Their residues and orientation are a stream's state, so a stream rested
    /// before the join is rested again. Refused when strands are already joined or at another
    /// tower's shape.
    pub fn join_strands(&mut self, strands: Strands) -> Result<()> {
        if self.strands.is_some() {
            return refuse("a tower takes one set of strands");
        }
        let d = &self.declaration;
        if (strands.levels, strands.alphabet, strands.modes) != (d.levels, d.alphabet, d.modes) {
            return refuse("strands of another tower's shape");
        }
        let layout = Layout::new(d, self.pair.as_ref().map_or(0, PairFace::forms), self.ring.as_ref().map_or(0, RingFace::ranks), self.ring.as_ref().map_or(0, RingFace::harmonics), strands.parts());
        self.theta.resize(layout.len, 0);
        self.layout = layout;
        self.strands = Some(strands);
        Ok(())
    }

    /// [derived; agent-inferred, October 27] **The pair contacts opened on the strands'
    /// comparison** (record §7): the located comparison `(e_s r_s + e_t r_t) mod q_L` of strands
    /// `s` and `t` has the face `e^(2πi e_s r_s/q) e^(2πi e_t r_t/q)`, whose parts are four products
    /// of one strand's part by the other's,
    ///
    /// ```text
    /// Re = cos_s cos_t − e_s e_t sin_s sin_t,     Im = e_s sin_s cos_t + e_t cos_s sin_t
    /// ```
    ///
    /// so contacts `4i..4i + 4` of the strands' level, for ring `i`, are opened to conduct exactly
    /// `cos_s cos_t`, `e_s e_t sin_s sin_t`, `e_s sin_s cos_t` and `e_t cos_s sin_t`: their `W_a`,
    /// `W_b`, `b_a` and `b_b` at zero, and `W_sa`, `W_sb` one on the factors, on the material's
    /// grain. The return and the readout read the comparison from there; every other family is as
    /// it was. Refused without strands, under a contact law other than the pair, for a comparison
    /// that is not of two strands each signed `±1`, or with fewer than four contacts a ring.
    pub fn open_strands_comparison(&mut self, compared: [usize; 2], signs: [i8; 2]) -> Result<()> {
        let d = self.declaration;
        let Some(strands) = &self.strands else {
            return refuse("a comparison opens on joined strands");
        };
        if d.contact != ContactLaw::Pair {
            return refuse("a comparison is a pair contact's product: it opens under the pair law");
        }
        if compared.iter().any(|&s| s > 2) || compared[0] == compared[1] || signs.iter().any(|&e| e != 1 && e != -1) {
            return refuse("a comparison of two strands, each signed ±1");
        }
        let (w, rings, c) = (d.width, strands.rings.len(), strands.parts());
        if d.contacts < 4 * rings {
            return refuse("a comparison opens four contacts a ring");
        }
        let lv = self.layout.levels[strands.level];
        let unit = 1i32 << MATERIAL_BITS;
        let (s, t) = (compared[0], compared[1]);
        let (es, et) = (i32::from(signs[0]), i32::from(signs[1]));
        for i in 0..rings {
            // Residue j's real part at 2j, its imaginary part at 2j + 1.
            let (cs, ct) = (2 * (s * rings + i), 2 * (t * rings + i));
            let products = [((cs, 1), (ct, 1)), ((cs + 1, es), (ct + 1, et)), ((cs + 1, es), (ct, 1)), ((cs, 1), (ct + 1, et))];
            for (j, ((a, ea), (b, eb))) in products.into_iter().enumerate() {
                let o = 4 * i + j;
                self.theta[lv.contact + o * w..lv.contact + (o + 1) * w].fill(0);
                self.theta[lv.pair + o * w..lv.pair + (o + 1) * w].fill(0);
                self.theta[lv.contact_bias + o] = 0;
                self.theta[lv.pair_bias + o] = 0;
                let (sa, sb) = (self.layout.strand_contact + o * c, self.layout.strand_pair + o * c);
                self.theta[sa..sa + c].fill(0);
                self.theta[sb..sb + c].fill(0);
                self.theta[sa + a] = ea * unit;
                self.theta[sb + b] = eb * unit;
            }
        }
        Ok(())
    }

    /// The strands, when they are joined.
    pub fn strands(&self) -> Option<&Strands> {
        self.strands.as_ref()
    }

    /// [agent-inferred, October 25] **The ring's readout opened at its founding**: `W` (`A` rows
    /// of the face's channels, on the material's `2^(−24)`) replaces the readout, so the ring
    /// carries code from the first cell and its covector reaches the tower from the first section
    /// (a readout at zero returns none, and one pass of the tower's own learning dephased the ring
    /// before its readout could read it). Refused without a ring face or at another shape.
    pub fn open_ring_readout(&mut self, readout: &[i32]) -> Result<()> {
        let k = self.ring.as_ref().map_or(0, |face| face.channels(self.declaration.width));
        if k == 0 || readout.len() != self.declaration.alphabet * k {
            return refuse("a ring readout needs a ring face and one row of its channels a class");
        }
        let rr = self.layout.ring_readout;
        self.theta[rr..rr + readout.len()].copy_from_slice(readout);
        Ok(())
    }

    /// The material the ring's push reads (none without a ring face): what carries the face `ŝ`
    /// it pushes from and the move it rides. That is the encoding and the pair face's lift into
    /// it, every family of the levels below the ring's (they make its level's input), and its own
    /// level's moves, pushes, gates, turns and pumps (its read, contacts and return make the next
    /// level's input, not its modes).
    pub fn ring_read_families(&self) -> Vec<std::ops::Range<usize>> {
        let Some(face) = &self.ring else { return Vec::new() };
        let (l, d) = (&self.layout, &self.declaration);
        let (n, w) = (d.modes, d.width);
        let mut families = vec![l.encoding..l.encoding + d.alphabet * w];
        if let Some(pair) = &self.pair {
            families.push(l.pair_encoding..l.pair_encoding + w * pair.forms());
        }
        let lv = l.levels[face.level];
        families.push(l.levels[0].move_re..lv.move_re);
        families.extend([lv.move_re..lv.move_re + n, lv.move_im..lv.move_im + n, lv.push_re..lv.push_re + n * w, lv.push_im..lv.push_im + n * w]);
        if d.gated {
            families.extend([lv.gate..lv.gate + n * w, lv.gate_bias..lv.gate_bias + n]);
        }
        if d.turned {
            families.extend([lv.turn..lv.turn + n * w, lv.turn_bias..lv.turn_bias + n]);
        }
        if d.pumped {
            families.extend([lv.pump..lv.pump + n * w, lv.pump_bias..lv.pump_bias + n, lv.pump_axis..lv.pump_axis + n * w, lv.pump_axis_bias..lv.pump_axis_bias + n]);
        }
        families
    }

    /// Where the tower's own readout and its bias lie in the material.
    pub fn readout_family(&self) -> std::ops::Range<usize> {
        self.layout.readout..self.layout.readout_bias + self.declaration.alphabet
    }

    /// Where the whole ring lies in the material (none without a ring face): its readout `W` and
    /// then its factors, whose moments its founding opens ([`TowerLearner::open_moments`]).
    pub fn ring_family(&self) -> Option<std::ops::Range<usize>> {
        Some(self.layout.ring_readout..self.ring_factor_family()?.end)
    }

    /// Where the ring's factors lie in the material (none without a ring face): `R` ranks of
    /// [`rank_material`], each `a₀, a₁, b₀, b₁, g`.
    pub fn ring_factor_family(&self) -> Option<std::ops::Range<usize>> {
        let face = self.ring.as_ref()?;
        let rf = self.layout.ring_factors;
        Some(rf..rf + face.ranks() * rank_material(&self.declaration))
    }

    /// Rank `r` of the ring as the material holds its factors (none without a ring face or rank).
    pub fn ring_rank(&self, r: usize) -> Option<RingRank> {
        let face = self.ring.as_ref()?;
        let family = self.ring_factor_family()?;
        face.ranks_of(&self.declaration, &self.theta[family]).into_iter().nth(r)
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
///
/// [definition; agent-inferred, October 27] **The certificate decided by partition.** The products
/// are compared through their logarithms first: each numerator and denominator `v` is read on
/// `2^(−CERTIFICATE_DIGITS)` ([`log2_reading`]), whose reading lies within `CERTIFICATE_SLACK`
/// grains of `log₂ v`. When the two sides' summed readings differ by more than every reading's
/// slack together, the sign of the difference is the sign of `log₂ Π p_new − log₂ Π p_old`, and so
/// the answer of the exact comparison; only inside that band are the products formed
/// ([`fewer_bits_exact`]). The answer is always the exact comparison's: the readings partition the
/// sections into those they decide and those the products decide. The readings are an integer sum,
/// so any partition of the faces sums them to the same bits. Measured October 25, the products
/// took 0.5 s a section at 320 streams and bounded the card's pass. The readings hold for positive
/// values only: a zero mass or total (never a face's, whose masses are at least one; Epime's review
/// of October 27 named the witness `[(0, 3)]` against `[(0, 2)]`) is decided by the products.
fn fewer_bits(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    if old.iter().chain(new).any(|&(m, t)| m == 0 || t == 0) {
        return fewer_bits_exact(old, new);
    }
    let side = |faces: &[(u128, u128)]| -> i128 { faces.iter().map(|&(m, t)| log2_reading(m) - log2_reading(t)).sum() };
    let difference = side(new) - side(old);
    let slack = CERTIFICATE_SLACK * 2 * (old.len() + new.len()) as i128;
    if difference > slack {
        return checked(true, old, new);
    }
    if difference < -slack {
        return checked(false, old, new);
    }
    fewer_bits_exact(old, new)
}

/// A decision the readings made. Built with the `certificate-check` feature, it is compared with the
/// products and a disagreement stops the run: the acceptance read that the partition decides as the
/// products do on every call of a whole pass. Without the feature it is the decision.
fn checked(decided: bool, old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    #[cfg(feature = "certificate-check")]
    assert_eq!(decided, fewer_bits_exact(old, new), "the certificate's readings decided against its products");
    let _ = (old, new);
    decided
}

/// The fractional digits of the certificate's logarithmic readings.
const CERTIFICATE_DIGITS: u32 = 32;

/// How far a reading may lie from `log₂ v`, in grains of `2^(−CERTIFICATE_DIGITS)`. With `μ` the
/// mantissa, `d_k` the digits and `ε_k ≥ 0` the logarithm each release at `2^(−62)` takes off
/// (`ε_k < 2^(−61)`, the mantissa staying in `[1, 2)`), the squarings unroll to
/// `log₂ μ = Σ_(k≤K) 2^(−k) d_k + 2^(−K) log₂ μ_K + Σ_(k≤K) 2^(−k) ε_k`, so a reading lies below
/// `log₂ v` by less than one grain and `2^(−60)` (the entry release included), never above it;
/// three grains hold that with room.
const CERTIFICATE_SLACK: i128 = 3;

/// `log₂ v` for `v ≥ 1` on `2^(−CERTIFICATE_DIGITS)`: the whole part from `v`'s width, then the
/// mantissa's binary digits by squaring (released at `2^(−62)`), halving it when it passes two.
/// A `v` wider than 63 bits enters through its leading 63 (a relative release below `2^(−62)`).
fn log2_reading(v: u128) -> i128 {
    let v = v.max(1);
    let width = 128 - v.leading_zeros();
    let mut mantissa = if width > 63 { v >> (width - 63) } else { v << (63 - width) }; // in [2^62, 2^63)
    let mut fraction = 0i128;
    for _ in 0..CERTIFICATE_DIGITS {
        mantissa = (mantissa * mantissa) >> 62;
        fraction <<= 1;
        if mantissa >= 1u128 << 63 {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    ((width as i128 - 1) << CERTIFICATE_DIGITS) + fraction
}

/// The products themselves: `Π m_new · Π t_old > Π m_old · Π t_new`.
fn fewer_bits_exact(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
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

/// A covector entry on the deposit's grain `2^(−32)` from its family's natural grain: a material
/// family's `Σ δz x` on `2^(−40)` is released, a face family's `Σ δz` on `2^(−24)` raised. The moves
/// step through their chart ([`Tower::to_move_chart`]) and are not read here.
fn on_step_grain(grain: u32, v: i128) -> i128 {
    if grain == MATERIAL_BITS {
        release(v, COVECTOR_BITS + FACE_BITS - STEP_BITS)
    } else {
        v << (STEP_BITS - COVECTOR_BITS)
    }
}

/// The deposit's step for one entry: its first moment `m` (on `2^(−32)`) over the root of its
/// second `v`, at the rate `2^(−rate)`, on its family's own grain:
/// `((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)`, before the certificate halves it.
fn deposit_step(m: i128, v: i128, grain: u32, rate: u32) -> i128 {
    deposit_over(m, deposit_root(v), grain, rate)
}

/// The deposit's divisor for a second moment `v`: `⌊√v⌋ + 1`.
fn deposit_root(v: i128) -> i128 {
    (v.max(0) as u128).isqrt() as i128 + 1
}

/// The deposit's step for a first moment `m` over its second moment's divisor `root`.
fn deposit_over(m: i128, root: i128, grain: u32, rate: u32) -> i128 {
    ((m << grain) >> rate) / root
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

/// One level of [`Tower::bilinear_modes`]: each drive's weight on each entry (`2^(−48)`) and the
/// bilinear block between entries (`2^(−96)`), rows the first drive's. The entries are the level's
/// modes and, on the strands' level, each strand residue's face after them ([`Strands::residues`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BilinearModes {
    pub first: Vec<BigUint>,
    pub second: Vec<BigUint>,
    pub block: Vec<Vec<BigUint>>,
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
    /// [agent-inferred, October 25] Families a section reads and does not deposit: a run's
    /// declared hold (a foil that separates which families' steps carry a change), never written
    /// with the learner. The moments still move there, so released, a family steps on its own
    /// statistics.
    pub held: Vec<std::ops::Range<usize>>,
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
        Self { tower, first: vec![0; len], second: vec![0; len], opened: false, rate_bits, swell: Vec::new(), held: Vec::new() }
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
        self.section_realized(states, classes, compared, &mut HostPass::default())
    }

    /// The section of [`TowerLearner::section_compared`] with its forward and reverse read through a
    /// declared [`PassRealization`] (`realization`'s module header); every realization returns the
    /// host's bits, so the receipt and the learner are the host's.
    pub fn section_realized(&mut self, states: &mut [TowerState], classes: &[&[usize]], compared: Option<&[&[Option<usize>]]>, realization: &mut dyn PassRealization) -> Result<SectionReceipt> {
        if states.len() != classes.len() || classes.iter().any(|c| c.len() < 2) {
            return refuse("a section needs one carried state and two classes a stream");
        }
        if compared.is_some_and(|m| m.len() != classes.len() || m.iter().zip(classes).any(|(m, c)| m.len() != c.len())) {
            return refuse("a comparison for each class of each stream");
        }
        let target = |s: usize, i: usize| compared.map_or(Some(classes[s][i]), |m| m[s][i]);
        let targets: Vec<Vec<Option<usize>>> = classes.iter().enumerate().map(|(s, c)| (1..c.len()).map(|i| target(s, i)).collect()).collect();
        self.tower.admit_read(classes, &targets)?;
        let opening: Vec<TowerState> = states.to_vec();
        let read = realization.forward(&self.tower, &opening, classes, &targets, Slot::Opened)?;
        self.swell = read.swell;
        let faces_old: Vec<(u128, u128)> = read.faces.iter().flatten().flatten().copied().collect();
        let part_codes = |faces: &[Vec<Option<(u128, u128)>>]| -> Vec<i64> { faces.iter().map(|cells| cells.iter().flatten().map(|&(m, t)| face_code(m, t)).sum::<i64>()).collect() };
        let parts_before = part_codes(&read.faces);
        let code_before: i64 = parts_before.iter().sum();
        let tower = &self.tower;
        let mut g = realization.reverse(tower, &opening, classes, compared)?;
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
                let q = deposit_step(self.first[i], self.second[i], grain, self.rate_bits);
                step[i] = if self.held.iter().any(|h| h.contains(&i)) { 0 } else { q };
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
                realization.carry(&self.tower, states, &opening, Slot::Opened)?;
                let parts = parts_before.iter().map(|&c| (c, c)).collect();
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after: code_before, halvings, deposited: false, parts });
            }
            candidate.project();
            let reread = realization.forward(&candidate, &opening, classes, &targets, Slot::Reread)?;
            let faces_new: Vec<(u128, u128)> = reread.faces.iter().flatten().flatten().copied().collect();
            if fewer_bits(&faces_old, &faces_new) {
                let parts_after = part_codes(&reread.faces);
                let code_after: i64 = parts_after.iter().sum();
                let parts = parts_before.iter().copied().zip(parts_after).collect();
                realization.carry(&candidate, states, &opening, Slot::Reread)?;
                self.tower = candidate;
                return Ok(SectionReceipt { cells: faces_old.len(), code_before, code_after, halvings, deposited: true, parts });
            }
            halvings += 1;
        }
    }

    /// [definition; agent-inferred, October 25] **A founded family's moments, opened on the passage
    /// it was founded on.** The moments are the covector's running statistics, and a family opened
    /// with them at zero inside an opened learner claims a covector free of noise: the normalized
    /// step `m/√v` then moves every entry at two to four times the rate on the first sections,
    /// whatever its covector's sign carries, and a founded readout is undone before its moments
    /// learn its noise (measured: the ring's founded readout, 257 of 495 held-out units at the
    /// join, read 52 after one block pass, the held-out text 3.149 bits a byte against the foil's
    /// 2.690). The family's moments are therefore opened at the passage's own section statistics:
    /// each section of `sections` (one slice a stream, as a training section reads them) is read
    /// forward and back from the streams' carried states, without a deposit, and the family's
    /// entries take `first = Σ g / n` and `second = Σ g² / n` over its `n` sections, on the
    /// deposit's grain. Every other moment is left as carried. Returns `n`. A learner whose moments
    /// have not opened refuses: its first compared section opens every moment at that section's
    /// covector and square, so a family opened before it would be overwritten unread.
    pub fn open_moments(&mut self, family: std::ops::Range<usize>, states: &mut [TowerState], sections: &[Vec<&[usize]>]) -> Result<usize> {
        if !self.opened {
            return refuse("a family's moments open inside a learner whose moments have opened");
        }
        if family.end > self.tower.theta.len() || family.is_empty() || sections.is_empty() {
            return refuse("moments open on a family of the material over at least one section");
        }
        let (mut sum, mut squares) = (vec![0i128; family.len()], vec![0i128; family.len()]);
        for classes in sections {
            if classes.len() != states.len() || classes.iter().any(|c| c.len() < 2) {
                return refuse("a section needs one carried state and two classes a stream");
            }
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
            let gradients: Vec<Vec<i128>> = opening
                .par_iter()
                .zip(forwards.par_iter())
                .zip(classes.par_iter())
                .map(|((open, (cells, _)), c)| tower.reverse(open, cells, c, None))
                .collect::<Result<_>>()?;
            let mut g = vec![0i128; tower.theta.len()];
            for gs in &gradients {
                for (a, b) in g.iter_mut().zip(gs) {
                    *a += *b;
                }
            }
            tower.to_step_grain(&mut g);
            tower.to_move_chart(&mut g);
            for ((s, q), &v) in sum.iter_mut().zip(squares.iter_mut()).zip(&g[family.clone()]) {
                *s += v;
                *q = v.checked_mul(v).and_then(|v2| q.checked_add(v2)).ok_or(TowerError::Refused("a covector's squares outgrew their 128-bit carrier"))?;
            }
            tower.carry_credit(states, forwards, &opening, &reaches)?;
        }
        let n = sections.len() as i128;
        for (i, k) in family.enumerate() {
            self.first[k] = div_nearest(sum[i], n);
            self.second[k] = div_nearest(squares[i], n);
        }
        Ok(sections.len())
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
        let n = Tower::text_lines(text);
        if lines.len() != n + 3 {
            return refuse("a learner's text is its tower's lines and three of moments");
        }
        let tower = Tower::from_text(&lines[..n].iter().map(|l| format!("{l}\n")).collect::<String>())?;
        let lines = &lines[n - 2..];
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
        Ok(Self { tower, first, second, opened, rate_bits, swell: Vec::new(), held: Vec::new() })
    }

    /// The pair face joined to the learner's tower ([`Tower::join_pair_face`]), its families'
    /// moments opened at zero beside the moments the learner carries.
    pub fn join_pair_face(&mut self, face: PairFace) -> Result<()> {
        self.tower.join_pair_face(face)?;
        self.first.resize(self.tower.theta.len(), 0);
        self.second.resize(self.tower.theta.len(), 0);
        Ok(())
    }

    /// The ring face joined to the learner's tower ([`Tower::join_ring_face`]), its readout's
    /// moments opened at zero beside the moments the learner carries.
    pub fn join_ring_face(&mut self, face: RingFace) -> Result<()> {
        self.tower.join_ring_face(face)?;
        self.first.resize(self.tower.theta.len(), 0);
        self.second.resize(self.tower.theta.len(), 0);
        Ok(())
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

    /// [agent-inferred, October 25] **The ring reading**: the frozen tower reads `classes` from the
    /// state, and each cell's index, top face (what the readout reads), face (the masses of the
    /// class that arrives next) and, with a ring face joined, the ring's read (each rank's
    /// `(Re, Im)` released by its `read_shift`) and its face `ρ_t` (what the ring's readout reads)
    /// are handed to `each`. A reading beside the code: the tower is not moved.
    pub fn read_ring(&self, state: &mut TowerState, classes: &[usize], mut each: impl FnMut(usize, &[i32], &TowerFace, Option<(&[i64], &[i32])>) -> Result<()>) -> Result<()> {
        let reaches = self.reaches();
        for i in 0..classes.len().saturating_sub(1) {
            let cell = self.step(state, classes[i], &reaches)?;
            each(i, &cell.top, &cell.face, cell.ring_read.as_deref().zip(cell.ring.as_deref()))?;
        }
        Ok(())
    }

    /// [agent-inferred, October 24] **The circuit reading**: the frozen tower reads `classes` from
    /// the state, and each cell's [`CircuitCell`] (every level's stored, carried and pushed energy,
    /// its read's scale and its contacts' reach, and the code of the class that arrives next) is
    /// handed to `each`. A reading beside the code: the tower is not moved. The carried part is
    /// formed by the step's own law, `λ_t h + β_t h̄` released from `2^(−54)` to the state's grain,
    /// so `carried` is what the step adds the push to.
    pub fn read_circuit(&self, state: &mut TowerState, classes: &[usize], mut each: impl FnMut(usize, CircuitCell) -> Result<()>) -> Result<()> {
        let reaches = self.reaches();
        let n = self.declaration.modes;
        let t = &self.theta;
        for i in 0..classes.len().saturating_sub(1) {
            let opening = state.modes.clone();
            let cell = self.step(state, classes[i], &reaches)?;
            let mut levels = Vec::with_capacity(cell.levels.len());
            for (l, lc) in cell.levels.iter().enumerate() {
                let lv = &self.layout.levels[l];
                // The move acts on the stepped and turned state ([`Rotor`]).
                let moved = self.rotor.as_ref().map_or_else(|| Ok(opening[l].clone()), |r| r.moved(l, classes[i], &opening[l]))?;
                let modes: Vec<CircuitMode> = collect_exact((0..n).map(|k| {
                    let (hr, hi) = (moved[k].0 as i128, moved[k].1 as i128);
                    let lam = match lc.gate.get(k) {
                        Some(m) => m.lam,
                        None => (i64::from(t[lv.move_re + k]), i64::from(t[lv.move_im + k])),
                    };
                    let beta = lc.gate.get(k).map_or((0, 0), |m| m.beta);
                    let (lr, li, br, bi) = (lam.0 as i128, lam.1 as i128, beta.0 as i128, beta.1 as i128);
                    let carried = (fit64(release(lr * hr - li * hi + br * hr + bi * hi, MOVE_BITS))?, fit64(release(lr * hi + li * hr + bi * hr - br * hi, MOVE_BITS))?);
                    Ok(CircuitMode { before: opening[l][k], carried, after: lc.state[k], lam, beta })
                }))?;
                let carried: Vec<(i64, i64)> = modes.iter().map(|m| m.carried).collect();
                levels.push(CircuitLevel {
                    before: energy(&opening[l])?,
                    carried: energy(&carried)?,
                    after: energy(&lc.state)?,
                    scale: lc.read_scale,
                    drive: reach(&lc.drive).max(reach(&lc.pair)),
                    conduct: reach(&lc.conduct),
                    modes,
                });
            }
            each(i, CircuitCell { levels, code: cell.face.code(classes[i + 1]) })?;
        }
        Ok(())
    }

    /// [agent-inferred, October 24] **The input covectors**: the frozen tower reads `classes` from
    /// the state in sections of `section` cells, as a learner's stream does (each section's last
    /// coded class arrives first in the next), and each cell's [`InputCovector`] is handed to
    /// `each`: the state the arriving class meets, and the covector the section's reverse
    /// (`reverse_joined`, every face compared with the class that arrives) sends to its input. A
    /// reading beside the code: the tower is not moved, and the receiver keeps only its moment sums,
    /// never the cells.
    pub fn read_input_covectors(&self, state: &mut TowerState, classes: &[usize], section: usize, mut each: impl FnMut(InputCovector) -> Result<()>) -> Result<()> {
        if section == 0 {
            return refuse("a section of at least one cell");
        }
        if self.rotor.is_some() {
            return refuse("input covectors under a rotor: their carried face is the unstepped state the moves do not act on");
        }
        let reaches = self.reaches();
        let t = &self.theta;
        let mut start = 0;
        while start + 1 < classes.len() {
            let part = &classes[start..(start + section + 1).min(classes.len())];
            let opening = state.clone();
            let cells = self.forward(state, part, &reaches)?;
            let mut placed = Vec::new();
            let (_, dx) = self.reverse_joined(&opening, &cells, part, None, None, Some(&mut placed))?;
            let mut carried = carried_face(&opening.modes)?;
            for (i, (cell, covector)) in cells.iter().zip(&dx).enumerate() {
                let modes: Vec<i64> = placed.iter().flat_map(|level| level[i].iter().flat_map(|&(re, im)| [re, im])).collect();
                let moves: Vec<i64> = cell
                    .levels
                    .iter()
                    .zip(&self.layout.levels)
                    .flat_map(|(lc, lv)| {
                        (0..self.declaration.modes).flat_map(move |k| {
                            let lam = lc.gate.get(k).map_or((i64::from(t[lv.move_re + k]), i64::from(t[lv.move_im + k])), |m| m.lam);
                            let beta = lc.gate.get(k).map_or((0, 0), |m| m.beta);
                            [lam.0, lam.1, beta.0, beta.1]
                        })
                    })
                    .collect();
                each(InputCovector { class: part[i], carried: &carried, covector, modes: &modes, moves: &moves })?;
                let after: Vec<Vec<(i64, i64)>> = cell.levels.iter().map(|lc| lc.state.clone()).collect();
                carried = carried_face(&after)?;
            }
            start += part.len() - 1;
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
        let n = self.declaration.modes;
        let turns = turn_ladder(n);
        let rung = |k: usize| (k / turns).min(MARGIN as usize - 1);
        let rungs = rung(n - 1) + 1;
        let levels = self.bilinear_modes()?;
        Ok(levels
            .into_iter()
            .map(|level| {
                let mut e = vec![vec![BigUint::from(0u32); rungs]; rungs];
                // The modes' entries only: a strand's face has no rung.
                for (k, row) in level.block.into_iter().take(n).enumerate() {
                    for (k2, x) in row.into_iter().take(n).enumerate() {
                        e[rung(k)][rung(k2)] += x;
                    }
                }
                e
            })
            .collect())
    }

    /// [definition; agent-inferred, October 27] **The bilinear weight mode by mode**, the read
    /// [`Tower::bilinear_rungs`] sums over rungs: per level, `E_(k,k′) = Σ_o |A_(o,k)|² |B_(o,k′)|²`
    /// on `2^(−96)` and each drive's weight on each mode, `Σ_o |A_(o,k)|²` and `Σ_o |B_(o,k)|²` on
    /// `2^(−48)`. A coefficient multiplies the mode's face, so what a contact hears of a mode is its
    /// weight times the mode's loudness where it is read. On the strands' level each strand
    /// residue `j` is an entry after the modes, `n + j`, its coefficient the two parts of its face
    /// `|W_s(o, 2j)|² + |W_s(o, 2j + 1)|²`: the faces are at amplitude one ([`Strands`]), so the
    /// weight is what a contact hears of it. A rectifying tower has no bilinear block (a typed
    /// refusal).
    pub fn bilinear_modes(&self) -> Result<Vec<BilinearModes>> {
        let d = &self.declaration;
        if d.contact == ContactLaw::Rectifying {
            return refuse("a rectifying contact has no bilinear block");
        }
        let (w, n, f) = (d.width, d.modes, d.contacts);
        let t = &self.theta;
        let mut levels = Vec::with_capacity(self.layout.levels.len());
        for (l, lv) in self.layout.levels.iter().enumerate() {
            // |drive read back onto mode k|², per contact, on 2^(−48).
            let on_modes = |material: usize| -> Vec<Vec<u128>> {
                (0..f)
                    .map(|o| {
                        (0..n)
                            .map(|k| {
                                let (mut re, mut im) = (0i128, 0i128);
                                for i in 0..w {
                                    let m = t[material + o * w + i] as i128;
                                    re += m * t[lv.read_re + i * n + k] as i128;
                                    im += m * t[lv.read_im + i * n + k] as i128;
                                }
                                let (re, im) = (release(re, MATERIAL_BITS).unsigned_abs(), release(im, MATERIAL_BITS).unsigned_abs());
                                re * re + im * im
                            })
                            .collect()
                    })
                    .collect()
            };
            let (mut a, mut b) = (on_modes(lv.contact), on_modes(lv.pair));
            // The strand residues' faces after the modes, on their level: each part's coefficient
            // on 2^(−24), squared to 2^(−48).
            if let Some(strands) = self.strands.as_ref().filter(|strands| strands.level == l) {
                let c = strands.parts();
                for (drive, material) in [(&mut a, self.layout.strand_contact), (&mut b, self.layout.strand_pair)] {
                    for (o, row) in drive.iter_mut().enumerate() {
                        let at = material + o * c;
                        row.extend((0..c / 2).map(|j| {
                            let (re, im) = (t[at + 2 * j].unsigned_abs() as u128, t[at + 2 * j + 1].unsigned_abs() as u128);
                            re * re + im * im
                        }));
                    }
                }
            }
            let entries = a.first().map_or(n, Vec::len);
            let weight = |drive: &[Vec<u128>]| -> Vec<BigUint> { (0..entries).map(|k| drive.iter().map(|o| BigUint::from(o[k])).sum()).collect() };
            let mut block = vec![vec![BigUint::from(0u32); entries]; entries];
            for (ao, bo) in a.iter().zip(&b) {
                for (k, &x) in ao.iter().enumerate() {
                    if x == 0 {
                        continue;
                    }
                    let x = BigUint::from(x);
                    for (k2, &y) in bo.iter().enumerate() {
                        block[k][k2] += &x * BigUint::from(y);
                    }
                }
            }
            levels.push(BilinearModes { first: weight(&a), second: weight(&b), block });
        }
        Ok(levels)
    }
}

/// `m / t` on `2^(−62)`, at least one grain; a total past `2^64` is re-based so the shift fits.
fn unit_of(m: u128, t: u128) -> u128 {
    let shift = (128 - t.leading_zeros()).saturating_sub(64);
    (((m >> shift) << UNIT_BITS) / (t >> shift).max(1)).clamp(1, 1u128 << UNIT_BITS)
}

/// `−log₂(m / t)` on `2^(−20)` bits, for any face's mass and total.
pub fn code_of(m: u128, t: u128) -> i64 {
    -(log2_face(unit_of(m, t), READ_BITS) as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_certificates_reading_lies_within_one_grain_below_the_logarithm() {
        // floor(log₂ v · 2^32), read to 80 digits outside: a reading is it or one grain below.
        for (v, floor) in [
            (1u128, 0i128),
            (2, 1 << 32),
            (3, 6_807_362_105),
            (10, 14_267_572_527),
            (1_000_003, 85_605_453_752),
            ((1 << 100) + 12_345, 429_496_729_600),
            (u128::MAX, 549_755_813_887),
        ] {
            let r = log2_reading(v);
            assert!(r <= floor && r >= floor - 1, "{v}: {r} against {floor}");
        }
        for k in 0..128 {
            assert_eq!(log2_reading(1u128 << k), (k as i128) << CERTIFICATE_DIGITS);
        }
    }

    #[test]
    fn the_certificate_decided_by_partition_is_the_exact_comparison() {
        // A fixed integer sequence (splitmix64) of faces; the partition's answer is the products'.
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        };
        let mut face = |next: &mut dyn FnMut() -> u64| {
            let total = (next() as u128) << (next() % 12) | 1;
            let mass = (next() as u128 % total).max(1);
            (mass, total)
        };
        let (mut decided, mut fell_back) = (0, 0);
        for round in 0..400 {
            let n = 1 + round % 97;
            let old: Vec<(u128, u128)> = (0..n).map(|_| face(&mut next)).collect();
            let new: Vec<(u128, u128)> = match round % 4 {
                // unrelated faces
                0 => (0..n).map(|_| face(&mut next)).collect(),
                // the same faces in another order: equal products, never fewer bits
                1 => old.iter().rev().copied().collect(),
                // one mass moved by one: a difference far inside the slack
                2 => {
                    let mut v = old.clone();
                    let i = (next() as usize) % n;
                    v[i].0 = if next() % 2 == 0 { v[i].0 + 1 } else { (v[i].0 - 1).max(1) };
                    v
                }
                // every mass doubled where it stays below its total
                _ => old.iter().map(|&(m, t)| ((2 * m).min(t), t)).collect(),
            };
            let slack = CERTIFICATE_SLACK * 2 * (old.len() + new.len()) as i128;
            let side = |f: &[(u128, u128)]| -> i128 { f.iter().map(|&(m, t)| log2_reading(m) - log2_reading(t)).sum() };
            if (side(&new) - side(&old)).abs() > slack {
                decided += 1;
            } else {
                fell_back += 1;
            }
            assert_eq!(fewer_bits(&old, &new), fewer_bits_exact(&old, &new), "round {round}");
            assert_eq!(fewer_bits(&new, &old), fewer_bits_exact(&new, &old), "round {round}, reversed");
        }
        assert!(decided > 0 && fell_back > 0, "both sides of the partition are exercised: {decided} {fell_back}");
    }

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

    /// The scaled ladder divides rung `s`'s turn by `2^(s−1)` and leaves every other founded
    /// value as the fixed ladder draws it; both ladders split the bank between the two.
    #[test]
    fn a_scaled_ladder_divides_each_rungs_turn_by_its_memory_and_changes_only_the_moves() {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes: 32, contacts: 4, levels: 1, gated: true, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let k = keys(16384);
        let fixed = Tower::found(declaration, &k).expect("founded");
        let scaled = Tower::found_on(declaration, &k, TurnLadder::Scaled).expect("founded");
        let both = Tower::found_on(declaration, &k, TurnLadder::Both).expect("founded");
        let lv = fixed.layout.levels[0];
        let at = |t: &Tower, m: usize| (t.theta[lv.move_re + m] as i128, t.theta[lv.move_im + m] as i128);
        // Only the moves differ: the keys are drawn in one order whatever the ladder.
        let moved = |i: usize| (lv.move_re..lv.move_re + 32).contains(&i) || (lv.move_im..lv.move_im + 32).contains(&i);
        let rest = |t: &Tower| t.theta.iter().enumerate().filter(|&(i, _)| !moved(i)).map(|(_, &v)| v).collect::<Vec<_>>();
        assert_eq!(rest(&scaled), rest(&fixed));
        assert_eq!(rest(&both), rest(&fixed));
        // 32 modes: eight turns on four rungs. The first rung is one ladder's; on rung s the scaled
        // mode's turn, raised to the power 2^(s−1), is the first rung's (to a few grains).
        let one = 1i128 << MOVE_BITS;
        let unit = |(re, im): (i128, i128), s: u32| {
            let rho = one - (one >> s);
            (div_nearest(re * one, rho), div_nearest(im * one, rho))
        };
        for m in 0..32 {
            let (s, j) = ((m / 8) as u32 + 1, m % 8);
            let mut u = unit(at(&scaled, m), s);
            for _ in 1..s {
                u = (release(u.0 * u.0 - u.1 * u.1, MOVE_BITS), release(2 * u.0 * u.1, MOVE_BITS));
            }
            let first = unit(at(&fixed, j), 1);
            assert!((u.0 - first.0).abs() < 1 << 12 && (u.1 - first.1).abs() < 1 << 12, "mode {m}: {u:?} against {first:?}");
            if s == 1 {
                assert_eq!(at(&scaled, m), at(&fixed, m));
            }
        }
        // Both: the first half is the fixed ladder over two rungs, the second the scaled one.
        for m in 0..16 {
            assert_eq!(at(&both, m), at(&fixed, m));
            assert_eq!(at(&both, 16 + m), at(&scaled, m));
        }
        let odd = TowerDeclaration { modes: 3, ..declaration };
        assert!(Tower::found_on(odd, &k, TurnLadder::Both).is_err());
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
        tiny_shaped(levels, 2, gated, turned, pumped, contact)
    }

    /// [`tiny_declared`] with `modes` modes a level.
    fn tiny_shaped(levels: usize, modes: usize, gated: bool, turned: bool, pumped: bool, contact: ContactLaw) -> Tower {
        tiny_contacts(levels, modes, 4, gated, turned, pumped, contact)
    }

    /// [`tiny_shaped`] with `contacts` contacts a level (four reads as [`tiny_shaped`]).
    fn tiny_contacts(levels: usize, modes: usize, contacts: usize, gated: bool, turned: bool, pumped: bool, contact: ContactLaw) -> Tower {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes, contacts, levels, gated, turned, pumped, contact };
        let (nw, fw) = (modes * declaration.width, contacts * declaration.width);
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
            fill(&mut tower.theta, lv.ret, fw);
        }
        if gated {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.gate, nw);
                for v in &mut tower.theta[lv.gate..lv.gate + nw] {
                    *v *= 8;
                }
            }
        }
        if turned {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.turn, nw);
                for v in &mut tower.theta[lv.turn..lv.turn + nw] {
                    *v *= 8;
                }
            }
        }
        if contact != ContactLaw::Rectifying {
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.pair, fw);
            }
        }
        if pumped {
            // The pump's depth at some tenths, its axis turned by a few half turns (measured: at
            // |κ| near ½ the quadrature is shed and the gate's covector falls below the reading;
            // the axis's covector scales with |β|).
            for lv in &layout.levels {
                fill(&mut tower.theta, lv.pump, nw);
                fill(&mut tower.theta, lv.pump_axis, nw);
                for v in &mut tower.theta[lv.pump..lv.pump + nw] {
                    *v *= 4;
                }
                for v in &mut tower.theta[lv.pump_axis..lv.pump_axis + nw] {
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

    /// The circuit reading's energies are the forward's: `before` is the state's energy before the
    /// class arrives, `after` the energy of the state the step leaves, `carried` what the moves
    /// keep (so the level dissipates, summed over the passage), the code is the frozen reading's,
    /// and the reading moves the state as the forward does; on gated, turned and pumped modes and
    /// on the ungated tower.
    #[test]
    fn the_circuit_readings_energies_are_the_forwards() {
        for tower in [tiny_declared(2, true, true, true, ContactLaw::Pair), tiny()] {
            let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
            let reaches = tower.reaches();
            let mut state = tower.rest();
            let mut states = vec![state.clone()];
            for &u in &classes[..classes.len() - 1] {
                tower.step(&mut state, u, &reaches).expect("step");
                states.push(state.clone());
            }
            let codes = tower.read_cells(&mut tower.rest(), &classes).expect("codes");
            let mut read = tower.rest();
            let (mut lost, mut count) = (vec![0i128; tower.declaration.levels], 0);
            tower
                .read_circuit(&mut read, &classes, |i, cell| {
                    assert_eq!(cell.code, codes[i]);
                    for (l, level) in cell.levels.iter().enumerate() {
                        assert_eq!(level.before, energy(&states[i].modes[l]).expect("energy"));
                        assert_eq!(level.after, energy(&states[i + 1].modes[l]).expect("energy"));
                        let modes = |f: fn(&CircuitMode) -> (i64, i64)| level.modes.iter().map(f).collect::<Vec<_>>();
                        assert_eq!(modes(|m| m.before), states[i].modes[l]);
                        assert_eq!(modes(|m| m.after), states[i + 1].modes[l]);
                        assert_eq!(level.carried, energy(&modes(|m| m.carried)).expect("energy"));
                        lost[l] += level.before as i128 - level.carried as i128;
                    }
                    count += 1;
                    Ok(())
                })
                .expect("read");
            assert_eq!(count, classes.len() - 1);
            assert!(lost.iter().all(|&d| d > 0));
            assert_eq!(read, state);
        }
    }

    /// The input covectors are the reverse's: summed class by class over a section they are the
    /// encoding's covector, each cell's carried face is the state its class meets, and the reading
    /// moves the state as the forward does; read in shorter sections, each section's sum is its
    /// own reverse's, and the sections continue the one passage. Beside each cell's covector the
    /// reverse hands its covector to every level's modes, one `(re, im)` per mode.
    #[test]
    fn the_input_covectors_sum_to_the_encodings_covector() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let (a, w) = (tower.declaration.alphabet, tower.declaration.width);
        let reaches = tower.reaches();
        let mut state = tower.rest();
        let mut states = vec![state.clone()];
        for &u in &classes[..classes.len() - 1] {
            tower.step(&mut state, u, &reaches).expect("step");
            states.push(state.clone());
        }
        let mut circuit = Vec::new();
        tower
            .read_circuit(&mut tower.rest(), &classes, |_, cell| {
                circuit.push(cell);
                Ok(())
            })
            .expect("circuit");
        for section in [classes.len() - 1, 5, 1] {
            let mut expected = vec![0i128; a * w];
            let mut open = tower.rest();
            let mut start = 0;
            while start + 1 < classes.len() {
                let part = &classes[start..(start + section + 1).min(classes.len())];
                let opening = open.clone();
                let cells = tower.forward(&mut open, part, &reaches).expect("forward");
                let g = tower.reverse(&opening, &cells, part, None).expect("reverse");
                for (slot, &v) in expected.iter_mut().zip(&g[tower.layout.encoding..tower.layout.encoding + a * w]) {
                    *slot += v;
                }
                start += part.len() - 1;
            }
            let (mut summed, mut count, mut moved) = (vec![0i128; a * w], 0, false);
            let mut read = tower.rest();
            tower
                .read_input_covectors(&mut read, &classes, section, |cell| {
                    assert_eq!(cell.class, classes[count]);
                    assert_eq!(cell.carried, &carried_face(&states[count].modes).expect("face")[..]);
                    assert_eq!(cell.modes.len(), 2 * states[count].modes.iter().map(Vec::len).sum::<usize>());
                    let circuit: Vec<i64> = circuit[count].levels.iter().flat_map(|l| l.modes.iter().flat_map(|m| [m.lam.0, m.lam.1, m.beta.0, m.beta.1])).collect();
                    assert_eq!(cell.moves, &circuit[..]);
                    moved |= cell.modes.iter().any(|&v| v != 0);
                    for (slot, &v) in summed[cell.class * w..(cell.class + 1) * w].iter_mut().zip(cell.covector) {
                        *slot += v as i128;
                    }
                    count += 1;
                    Ok(())
                })
                .expect("read");
            assert_eq!(count, classes.len() - 1);
            assert!(summed.iter().any(|&v| v != 0));
            assert!(moved);
            assert_eq!(summed, expected);
            assert_eq!(read, state);
        }
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

    /// The tiny rotor's rings on four modes a level: a ring of one mode modulo 9 and a ring of two
    /// modes modulo 11, the fourth mode still.
    const TINY_RINGS: [RotorRing; 2] = [RotorRing { width: 1, modulus: 9 }, RotorRing { width: 2, modulus: 11 }];

    /// The tiny rotor's keys on a two-level tower of four classes, `(steps, turns)`: at the first
    /// level class 1 steps the ring of two by one and turns as the digit 1 (`1`, `1`, `10`), class 2
    /// turns as the digit 2 without a step (`2`, `2`, `9`) and class 3 steps without a turn (the
    /// generator alone); at the second class 3 steps and turns (`5`, `3`, `8`). Class 0 is still.
    fn tiny_keys() -> (Vec<u32>, Vec<u32>) {
        let mut steps = vec![0u32; 2 * 4 * 2];
        let mut turns = vec![0u32; 2 * 4 * 3];
        steps[2 + 1] = 1;
        turns[3..6].copy_from_slice(&[1, 1, 10]);
        turns[6..9].copy_from_slice(&[2, 2, 9]);
        steps[6 + 1] = 1;
        steps[14 + 1] = 1;
        turns[21..24].copy_from_slice(&[5, 3, 8]);
        (steps, turns)
    }

    /// The pumped tiny tower of four modes a level with [`tiny_keys`]' rotor.
    fn tiny_rotor() -> Tower {
        rotor_on(tiny_shaped(2, 4, true, true, true, ContactLaw::Rectifying))
    }

    /// [`tiny_keys`]' rotor on a two-level tower of four modes a level.
    fn rotor_on(mut tower: Tower) -> Tower {
        let (steps, turns) = tiny_keys();
        tower.join_rotor(Rotor::new(&tower.declaration, TINY_RINGS.to_vec(), steps, turns).expect("rotor")).expect("joined");
        tower
    }

    #[test]
    fn a_rotor_tower_restores_exactly() {
        let tower = tiny_rotor();
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let learner = TowerLearner::new(tower.clone(), 7);
        assert_eq!(TowerLearner::from_text(&learner.to_text()).expect("restored").tower, tower);
        let mut opened = tiny_shaped(2, 4, true, true, true, ContactLaw::Rectifying);
        opened.join_rotor(Rotor::opening(&opened.declaration)).expect("joined");
        assert_eq!(Tower::from_text(&opened.to_text()).expect("restored"), opened);
        let declaration = tower.declaration;
        let rings = TINY_RINGS.to_vec();
        let (steps, turns) = tiny_keys();
        let refused = |rings: Vec<RotorRing>, steps: Vec<u32>, turns: Vec<u32>| Rotor::new(&declaration, rings, steps, turns).is_err();
        // A step at the width of its ring, a turn at the modulus of its ring.
        let mut wide = steps.clone();
        wide[2] = 1;
        assert!(refused(rings.clone(), wide, turns.clone()));
        let mut over = turns.clone();
        over[3] = 9;
        assert!(refused(rings.clone(), steps.clone(), over));
        // Keys of the wrong count, rings that do not fit, a ring without a mode or a modulus.
        assert!(refused(rings.clone(), steps[1..].to_vec(), turns.clone()));
        assert!(refused(rings.clone(), steps.clone(), turns[1..].to_vec()));
        assert!(refused(vec![RotorRing { width: 5, modulus: 9 }], vec![0; 8], vec![0; 40]));
        assert!(refused(vec![RotorRing { width: 0, modulus: 9 }], vec![0; 8], Vec::new()));
        assert!(refused(vec![RotorRing { width: 1, modulus: 1 }], vec![0; 8], vec![0; 8]));
        // The text of another tower's rotor.
        let text = tower.to_text().replace("rotor 2 4 4 ", "rotor 2 4 3 ");
        assert!(Tower::from_text(&text).is_err());
    }

    /// A rotor that steps and turns nothing reads every passage as its twin without one, with or
    /// without rings.
    #[test]
    fn a_still_rotor_opens_on_its_twin() {
        let twin = tiny_shaped(2, 4, true, true, true, ContactLaw::Rectifying);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let mut still = twin.clone();
        still.join_rotor(Rotor::opening(&still.declaration)).expect("joined");
        assert_eq!(code(&still, &classes), code(&twin, &classes));
        let mut ringed = twin.clone();
        ringed.join_rotor(Rotor::new(&ringed.declaration, TINY_RINGS.to_vec(), vec![0; 16], vec![0; 24]).expect("rotor")).expect("joined");
        assert_eq!(code(&ringed, &classes), code(&twin, &classes));
        assert_ne!(code(&tiny_rotor(), &classes), code(&twin, &classes));
    }

    /// One cell of the rotor tower is its twin's cell from the stepped and turned state: the move
    /// acts on `T P^σ h`, and nothing else in the cell reads the state before it.
    #[test]
    fn a_rotor_steps_and_turns_each_ring_before_the_move() {
        let rotor_tower = tiny_rotor();
        let twin = tiny_shaped(2, 4, true, true, true, ContactLaw::Rectifying);
        let rotor = rotor_tower.rotor().expect("rotor").clone();
        let mut s = rotor_tower.rest();
        for &u in &[0usize, 2, 1, 3, 3] {
            rotor_tower.advance(&mut s, u).expect("advance");
        }
        for u in 0..4 {
            let mut moved = s.clone();
            let face = rotor_tower.advance(&mut moved, u).expect("advance");
            let mut stepped = s.clone();
            stepped.modes = (0..2).map(|l| rotor.moved(l, u, &s.modes[l]).expect("moved")).collect();
            let twin_face = twin.advance(&mut stepped, u).expect("advance");
            assert_eq!(moved, stepped, "class {u}");
            assert_eq!(face, twin_face, "class {u}");
        }
        // The generator alone is a permutation: mode s_k + j takes mode s_k + ((j + σ) mod w_k),
        // the ring of one mode and the still mode their own.
        let h = [(10, 1), (11, 2), (12, 3), (13, 4)];
        assert_eq!(rotor.moved(0, 3, &h).expect("moved"), vec![(10, 1), (12, 3), (11, 2), (13, 4)]);
        assert_eq!(rotor.moved(0, 0, &h).expect("moved"), h.to_vec());
    }

    /// A turn's face is its root of unity at the grain: nine turns by `1/9` of a turn, and eleven by
    /// `1/11`, return a state of ten units to itself within a few grains, and each face lies in the
    /// closed unit disk within two grains of its circle.
    #[test]
    fn a_rotor_turns_by_roots_of_unity() {
        let declaration = TowerDeclaration { alphabet: 1, width: 1, modes: 2, contacts: 1, levels: 1, gated: false, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let rotor = Rotor::new(&declaration, vec![RotorRing { width: 1, modulus: 9 }, RotorRing { width: 1, modulus: 11 }], vec![0, 0], vec![1, 1]).expect("rotor");
        let start = (10i64 << STATE_BITS, 3i64 << STATE_BITS);
        let mut h = vec![start, start];
        for _ in 0..9 {
            h = rotor.moved(0, 0, &h).expect("moved");
        }
        assert!((h[0].0 - start.0).abs() <= 16 && (h[0].1 - start.1).abs() <= 16, "{:?}", h[0]);
        for _ in 0..2 {
            h = rotor.moved(0, 0, &h).expect("moved");
        }
        assert!((h[1].0 - start.0).abs() <= 16 && (h[1].1 - start.1).abs() <= 16, "{:?}", h[1]);
        for q in [9u32, 11, 101] {
            for r in 0..q {
                let (a, b) = ring_face(r, q);
                let norm = a * a + b * b;
                assert!(norm <= 1i128 << (2 * MOVE_BITS) && norm >= (1i128 << (2 * MOVE_BITS)) - (4i128 << (MOVE_BITS + 1)), "{r}/{q}");
            }
        }
    }

    /// The reverse is the monomial's adjoint: `Re⟨g, T P^σ h⟩ = Re⟨(T P^σ)* g, h⟩` within the grains
    /// each side releases.
    #[test]
    fn a_rotor_reverse_is_its_adjoint() {
        let rotor = tiny_rotor().rotor().expect("rotor").clone();
        let k = keys(512);
        let word = |i: usize| i64::from(i32::from_be_bytes([k[4 * i], k[4 * i + 1], k[4 * i + 2], k[4 * i + 3]]) >> 12);
        for (l, u) in [(0usize, 1usize), (0, 2), (0, 3), (1, 3)] {
            let h: Vec<(i64, i64)> = (0..4).map(|m| (word(4 * m + 8 * u + l), word(4 * m + 1 + 8 * u + l))).collect();
            let g: Vec<(i128, i128)> = (0..4).map(|m| (i128::from(word(64 + 4 * m + u)), i128::from(word(65 + 4 * m + u)))).collect();
            let forward = rotor.moved(l, u, &h).expect("moved");
            let back = rotor.back(l, u, &g);
            let pair = |a: &[(i128, i128)], b: &[(i64, i64)]| a.iter().zip(b).map(|(&(x, y), &(p, q))| x * i128::from(p) + y * i128::from(q)).sum::<i128>();
            let bound: i128 = g.iter().map(|&(x, y)| x.abs() + y.abs()).sum::<i128>() + h.iter().map(|&(x, y)| i128::from(x.abs() + y.abs())).sum::<i128>();
            assert!((pair(&g, &forward) - pair(&back, &h)).abs() <= bound, "level {l} class {u}");
        }
    }

    /// A rotor beside a ring face, or a credited opening under a rotor, is refused: their laws
    /// under a step are owed.
    #[test]
    fn a_rotor_refuses_what_it_does_not_carry() {
        let mut tower = tiny_rotor();
        assert!(tower.join_rotor(Rotor::opening(&tower.declaration)).is_err());
        let opening = tower.rest_with_credit();
        let mut s = opening.clone();
        let classes = [0usize, 1, 2, 3];
        let cells = tower.forward(&mut s, &classes, &tower.reaches()).expect("forward");
        assert!(tower.reverse(&opening, &cells, &classes, None).is_err());
        let mut credit = opening.credit.clone().expect("credit");
        assert!(tower.advance_credit(&mut credit, &opening, &cells, &tower.reaches()).is_err());
        assert!(tower.read_input_covectors(&mut tower.rest(), &classes, 2, |_| Ok(())).is_err());
        tower.rotor = None;
        assert!(tower.join_rotor(Rotor::opening(&tower.declaration)).is_ok());
    }

    /// The strands on the staircase rings 9 and 99 (multipliers 1 and 10, the tenfold step), digit
    /// `d` turning each ring by `d`, the laws held, stepped and turned for strands `A`, `G`, `H`, and
    /// the record's keys: `<` clears `H` on the sheet `+1`, `+` and `-` hand `H` to `A` and clear it
    /// on the sheets `+1` and `−1`, and `=` hands `H` to `G` and `−A` to `H` on the sheet `+1`.
    fn tenfold_strands(declaration: &TowerDeclaration, level: usize, words: Vec<Vec<u8>>) -> Strands {
        let rings = vec![StrandRing { modulus: 9, multiplier: 1 }, StrandRing { modulus: 99, multiplier: 10 }];
        let digits = (0..10u32).map(|d| (b'0' + d as u8, vec![d % 9, d])).collect();
        let keys = vec![
            (b'+', StrandKey { source: [3, 2, 0], sheet: Sheet::Plus }),
            (b'-', StrandKey { source: [3, 2, 0], sheet: Sheet::Minus }),
            (b'<', StrandKey { source: [1, 2, 0], sheet: Sheet::Plus }),
            (b'=', StrandKey { source: [1, 3, -1], sheet: Sheet::Plus }),
        ];
        Strands::new(declaration, level, rings, [StrandLaw::Held, StrandLaw::Stepped, StrandLaw::Turned], digits, keys, words).expect("strands")
    }

    /// The equation at the consumer (the record's §2): from rest, after `<<x ∘ y =` and the first
    /// `k` digits of `z`, the comparison `H − G` on ring `len(z)` is `−10^k s_k`, `s_k` what is left
    /// of `x ± y` to write, so the tenth of its conjugate face is `z`'s next digit at every `k`, and
    /// the ring closes at `z`'s end; for every `x, y < 100` whose sum or difference is a positive
    /// numeral of one or two digits other than all nines. Words of several bytes read as their bytes
    /// in turn, and a byte with no turn and no key moves nothing.
    #[test]
    fn the_strands_read_the_comparison_chart() {
        let words: Vec<Vec<u8>> = ["<<12", "+3", "0=", "4", "2", " x"].iter().map(|w| w.as_bytes().to_vec()).collect();
        let declaration = TowerDeclaration { alphabet: words.len(), width: 1, modes: 6, contacts: 1, levels: 1, gated: false, turned: false, pumped: false, contact: ContactLaw::Rectifying };
        let strands = tenfold_strands(&declaration, 0, words);
        let read = |bytes: &[u8]| {
            let (mut r, mut reversed) = (vec![0u32; 6], false);
            for &b in bytes {
                strands.hear_byte(&mut r, &mut reversed, b);
            }
            (r, reversed)
        };
        // Strand `s` on ring `i` is `r[2s + i]`; the comparison `H − G` on ring `i`.
        let comparison = |r: &[u32], i: usize| -> u64 {
            let q = [9u64, 99][i];
            (u64::from(r[4 + i]) + q - u64::from(r[2 + i])) % q
        };
        let mut checked = 0;
        for x in 0..100u32 {
            for y in 0..100u32 {
                for (op, z) in [(b'+', x + y), (b'-', x.wrapping_sub(y))] {
                    if z == 0 || z >= 99 || z == 9 {
                        continue;
                    }
                    let digits = z.to_string().into_bytes();
                    let (i, q) = if digits.len() == 1 { (0, 9u64) } else { (1, 99u64) };
                    let mut bytes = b"<<".to_vec();
                    bytes.extend(x.to_string().bytes());
                    bytes.push(op);
                    bytes.extend(y.to_string().bytes());
                    bytes.push(b'=');
                    for k in 0..digits.len() {
                        let (r, reversed) = read(&bytes);
                        assert!(!reversed, "the sheet after the equals");
                        let conjugate = (q - comparison(&r, i)) % q;
                        assert_eq!(10 * conjugate / q, u64::from(digits[k] - b'0'), "{x} {} {y} = {z} at {k}", op as char);
                        bytes.push(digits[k]);
                    }
                    assert_eq!(comparison(&read(&bytes).0, i), 0, "{x} {} {y} = {z} closes", op as char);
                    checked += 1;
                }
            }
        }
        assert_eq!(checked, 9_797);
        // Words read as their bytes in turn; ` x` moves nothing.
        let (mut r, mut reversed) = (vec![0u32; 6], false);
        for class in 0..5 {
            strands.heard(&mut r, &mut reversed, class).expect("heard");
        }
        assert_eq!((r.clone(), reversed), read(b"<<12+30=42"));
        strands.heard(&mut r, &mut reversed, 5).expect("heard");
        assert_eq!((r, reversed), read(b"<<12+30=42"));
        // `50 - 8 =`: `y` is read on the reversed sheet, so `G` holds `−8`.
        let (r, _) = read(b"<<50-8=");
        assert_eq!((r[0], r[1], r[3]), (50 % 9, 50, 99 - 8));
    }

    /// The tiny strands read at `level` of a tower of four classes (`1`, `2`, `+`, `=`).
    fn tiny_strands(declaration: &TowerDeclaration, level: usize) -> Strands {
        tenfold_strands(declaration, level, vec![b"1".to_vec(), b"2".to_vec(), b"+".to_vec(), b"=".to_vec()])
    }

    /// The tower with the tiny strands read at its second level's contacts, opened on their
    /// comparison `H − G` when `opened`.
    fn stranded(mut tower: Tower, opened: bool) -> Tower {
        let strands = tiny_strands(&tower.declaration, 1);
        tower.join_strands(strands).expect("joined");
        if opened {
            tower.open_strands_comparison([2, 1], [1, -1]).expect("opened");
        }
        tower
    }

    /// The passage the strands' tests read: `1 2 + 2 1 = 1 2 + 1 = = 2`.
    /// The held-out read through a realization is the frozen read, code for code, whatever the
    /// window and however unequal the parts.
    #[test]
    fn a_realized_read_is_the_frozen_read_cell_by_cell() {
        let tower = tiny_of(true);
        let classes: Vec<usize> = (0..61usize).map(|i| (i * 7 + i / 3) % 4).collect();
        let parts: Vec<&[usize]> = classes.chunks(17).collect();
        let frozen: Vec<Vec<i64>> = parts.iter().map(|p| tower.read_cells(&mut tower.rest(), p).expect("read")).collect();
        for section in [1, 3, 16, 40] {
            let read = tower.read_parts_realized(&parts, section, &mut realization::HostPass::default()).expect("realized");
            assert_eq!(read, frozen, "section {section}");
        }
        assert!(tower.read_parts_realized(&parts, 0, &mut realization::HostPass::default()).is_err());
    }

    /// The certificate decides as the products do where a mass or total is zero (the readings'
    /// domain is positive values), and a read of a class outside the alphabet, or a comparison
    /// with one, is refused before the realization reads it.
    #[test]
    fn the_certificate_and_the_read_stay_in_their_domain() {
        assert!(!fewer_bits(&[(0, 3)], &[(0, 2)]));
        assert_eq!(fewer_bits(&[(0, 3)], &[(0, 2)]), fewer_bits_exact(&[(0, 3)], &[(0, 2)]));
        assert!(fewer_bits(&[(0, 3)], &[(1, 2)]));
        let tower = tiny_of(true);
        let a = tower.declaration.alphabet;
        let mut pass = realization::HostPass::default();
        let states = vec![tower.rest()];
        let classes: [&[usize]; 1] = [&[0, 1, 2]];
        assert!(pass.forward(&tower, &states, &classes, &[vec![Some(1), Some(a)]], Slot::Reread).is_err());
        let outside: [&[usize]; 1] = [&[0, a, 2]];
        assert!(pass.forward(&tower, &states, &outside, &[vec![Some(1), Some(2)]], Slot::Reread).is_err());
        assert!(pass.forward(&tower, &states, &classes, &[vec![Some(1), Some(2)]], Slot::Reread).is_ok());
    }

    /// The host's realization keeps no cell between its calls (but a credit-carrying stream's), so
    /// its reverse reads each stream's forward again: the summed covector is each stream's forward
    /// and reverse summed, and the carry is each stream's, its credit moved along its cells.
    #[test]
    fn the_host_pass_reads_each_stream_again_for_its_reverse() {
        let tower = tiny_of(true);
        let classes: [&[usize]; 3] = [&[0, 1, 2, 1], &[3, 0, 2, 2], &[1, 1, 3, 0]];
        let targets: Vec<Vec<Option<usize>>> = classes.iter().map(|c| c[1..].iter().map(|&u| Some(u)).collect()).collect();
        let opening = vec![tower.rest(), tower.rest_with_credit(), tower.rest()];
        let reaches = tower.reaches();
        let mut expected = vec![0i128; tower.theta.len()];
        let mut ends = Vec::new();
        for (open, c) in opening.iter().zip(&classes) {
            let mut end = open.clone();
            let cells = tower.forward(&mut end, c, &reaches).expect("forward");
            for (a, b) in expected.iter_mut().zip(tower.reverse(open, &cells, c, None).expect("reverse")) {
                *a += b;
            }
            ends.push((cells, end));
        }
        let mut carried = opening.clone();
        tower.carry_credit(&mut carried, ends, &opening, &reaches).expect("carry");
        let mut pass = realization::HostPass::default();
        pass.forward(&tower, &opening, &classes, &targets, Slot::Opened).expect("forward");
        assert_eq!(pass.reverse(&tower, &opening, &classes, None).expect("reverse"), expected);
        let mut states = opening.clone();
        pass.carry(&tower, &mut states, &opening, Slot::Opened).expect("carry");
        assert_eq!(states, carried);
        assert!(carried[1].credit != opening[1].credit);
    }

    /// The advance through a realization is [`Tower::advance`] class by class: the same faces,
    /// the same codes and the same continuing states, a prompt read whole and then one class at a
    /// time, on two streams at once.
    #[test]
    fn a_realized_advance_is_the_advance_class_by_class() {
        let tower = tiny_of(true);
        let prompts: [&[usize]; 2] = [&[0, 1, 2, 1, 3], &[3, 3, 0, 2, 1]];
        let mut host: Vec<TowerState> = (0..2).map(|_| tower.rest()).collect();
        let mut faces = Vec::new();
        let mut codes = Vec::new();
        for (s, prompt) in prompts.iter().enumerate() {
            let (mut face, mut code) = (None, 0i64);
            for &u in prompt.iter() {
                if let Some(f) = &face {
                    code += TowerFace::code(f, u);
                }
                face = Some(tower.advance(&mut host[s], u).expect("advance"));
            }
            faces.push(face.expect("a face"));
            codes.push(code);
        }
        let mut pass = realization::HostPass::default();
        let mut states: Vec<TowerState> = (0..2).map(|_| tower.rest()).collect();
        let (read, read_codes) = tower.advance_realized(&mut states, &prompts, &mut pass).expect("realized");
        assert_eq!((read, read_codes), (faces, codes));
        assert_eq!(states, host);
        for u in [2usize, 0, 3] {
            let expected: Vec<TowerFace> = host.iter_mut().map(|s| tower.advance(s, u).expect("advance")).collect();
            let (read, _) = tower.advance_realized(&mut states, &[&[u], &[u]], &mut pass).expect("realized");
            assert_eq!(read, expected);
            assert_eq!(states, host);
        }
        assert!(tower.advance_realized(&mut states, &[&[0, 1], &[2]], &mut pass).is_err());
    }

    /// The resident law names a joined rotor and joined strands, so a realization that reads
    /// neither (the card's) refuses such a tower instead of reading it as the plain one.
    #[test]
    fn the_resident_law_names_a_joined_rotor_and_strands() {
        let plain = tiny_contacts(2, 9, 4, true, false, false, ContactLaw::Rectifying);
        let law = plain.resident_law().expect("law");
        assert!(!law.rotor && !law.strands);
        let rotor = rotor_on(plain.clone()).resident_law().expect("law");
        assert!(rotor.rotor && !rotor.strands);
        let strands = stranded(plain, false).resident_law().expect("law");
        assert!(!strands.rotor && strands.strands);
    }

    const STRANDED: [usize; 13] = [0, 1, 2, 1, 0, 3, 0, 1, 2, 0, 3, 3, 1];

    /// Joined at zero, the strands' material reads nothing: on the rotor tower the modes and faces
    /// are its twin's without strands at every cell, and so is every family's covector, under each
    /// contact law, gated and pumped or not, while the strands hear every word (`=`'s key last, on
    /// the sheet `+1`) and their material takes a covector (`δa ⊗ s`, and `δb ⊗ s` under the pair
    /// law; the linear foil's second drive carries none at `b_a = 0`, as its twin's).
    #[test]
    fn strands_joined_at_zero_read_as_the_tower_without_them() {
        for (gated, contact) in [(true, ContactLaw::Rectifying), (false, ContactLaw::Pair), (true, ContactLaw::Pair), (false, ContactLaw::PairLinear)] {
            let twin = rotor_on(tiny_contacts(2, 9, 4, gated, gated, gated, contact));
            let tower = stranded(twin.clone(), false);
            let (mut s, mut t) = (tower.rest(), twin.rest());
            for &u in &STRANDED {
                assert_eq!(tower.advance(&mut s, u).expect("advance"), twin.advance(&mut t, u).expect("advance"), "class {u}");
                assert_eq!(s.modes, t.modes, "class {u}");
            }
            assert!(!s.reversed);
            assert_ne!(s.strands, vec![0; 6]);
            let covector = |tower: &Tower| {
                let opening = tower.rest();
                let mut s = opening.clone();
                let cells = tower.forward(&mut s, &STRANDED, &tower.reaches()).expect("forward");
                tower.reverse(&opening, &cells, &STRANDED, None).expect("reverse")
            };
            let (g, h) = (covector(&tower), covector(&twin));
            assert_eq!(g[..twin.layout.len], h[..]);
            let (sc, sp) = (tower.layout.strand_contact, tower.layout.strand_pair);
            assert!(g[sc..sc + 4 * 12].iter().any(|&x| x != 0));
            assert!(contact != ContactLaw::Pair || g[sp..sp + 4 * 12].iter().any(|&x| x != 0));
        }
    }

    /// Opened on the comparison `H − G`, contacts `4i..4i + 4` conduct exactly the four products of
    /// the two strands' faces on ring `i`, read at their level, and `(v₀ − v₁, v₂ + v₃)` is the
    /// comparison's face `e^(2πi (r_H − r_G)/q_i)` to the products' release; each drive's weight
    /// sits on its strand's residue alone, four units, and the block on the pair of them.
    #[test]
    fn the_opened_contacts_conduct_the_strands_comparison() {
        let tower = stranded(tiny_contacts(2, 9, 8, false, false, false, ContactLaw::Pair), true);
        let strands = tower.strands().expect("strands").clone();
        let reaches = tower.reaches();
        let half = half_turn(2 * MOVE_BITS);
        let mut s = tower.rest();
        let mut compared = 0;
        for &u in &STRANDED {
            let cell = tower.step(&mut s, u, &reaches).expect("step");
            let level = &cell.levels[1];
            assert_eq!(level.strands, strands.faces(&s.strands).expect("faces"));
            assert!(cell.levels[0].strands.is_empty());
            for (i, ring) in strands.rings().iter().enumerate() {
                let part = |j: usize| i128::from(level.strands[j]);
                let (h, g) = (2 * (2 * 2 + i), 2 * (2 + i));
                let products = [part(h) * part(g), -part(h + 1) * part(g + 1), part(h + 1) * part(g), -part(h) * part(g + 1)];
                for (j, p) in products.into_iter().enumerate() {
                    assert_eq!(i128::from(level.conduct[4 * i + j]), release(p, FACE_BITS), "class {u}, ring {i}, contact {j}");
                }
                let v = |j: usize| i128::from(level.conduct[4 * i + j]);
                let q = ring.modulus;
                let c = (s.strands[2 * 2 + i] + q - s.strands[2 + i]) % q;
                let (re, im) = ring_face_at(c, q, half);
                let (re, im) = (release(re, MOVE_BITS - FACE_BITS), release(im, MOVE_BITS - FACE_BITS));
                assert!((v(0) - v(1) - re).abs() <= 2 && (v(2) + v(3) - im).abs() <= 2, "class {u}, ring {i}: {} {} against {re} {im}", v(0) - v(1), v(2) + v(3));
                compared += usize::from(c != 0);
            }
        }
        assert!(compared > 0);
        let modes = &tower.bilinear_modes().expect("read")[1];
        let (n, rings) = (tower.declaration.modes, strands.rings().len());
        let zero = BigUint::from(0u32);
        let four: BigUint = BigUint::from(4u32) << 48u32;
        assert_eq!(modes.first.len(), n + 3 * rings);
        for j in 0..3 * rings {
            let (h, g) = (j / rings == 2, j / rings == 1);
            assert_eq!(modes.first[n + j], if h { four.clone() } else { zero.clone() }, "residue {j}");
            assert_eq!(modes.second[n + j], if g { four.clone() } else { zero.clone() }, "residue {j}");
        }
        assert!(modes.first[..n].iter().chain(&modes.second[..n]).all(|x| *x == zero));
        for i in 0..rings {
            assert_eq!(modes.block[n + 2 * rings + i][n + rings + i], BigUint::from(4u32) << 96u32);
        }
        assert_eq!(tower.bilinear_modes().expect("read")[0].first.len(), n);
    }

    #[test]
    fn a_strands_tower_restores_exactly() {
        let opened = stranded(tiny_contacts(2, 9, 8, false, false, false, ContactLaw::Pair), true);
        assert_eq!(Tower::from_text(&opened.to_text()).expect("restored"), opened);
        let tower = stranded(rotor_on(tiny_shaped(2, 11, true, true, true, ContactLaw::Rectifying)), false);
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let learner = TowerLearner::new(tower.clone(), 7);
        assert_eq!(TowerLearner::from_text(&learner.to_text()).expect("restored").tower, tower);
        // Strands with no digit and no key, an empty word among their words.
        let mut plain = tiny_shaped(2, 4, false, false, false, ContactLaw::Rectifying);
        let words = vec![Vec::new(), b"a".to_vec(), b"bc".to_vec(), vec![0, 255]];
        let ring = vec![StrandRing { modulus: 7, multiplier: 3 }];
        plain.join_strands(Strands::new(&plain.declaration, 1, ring, [StrandLaw::Turned; 3], Vec::new(), Vec::new(), words).expect("strands")).expect("joined");
        assert_eq!(Tower::from_text(&plain.to_text()).expect("restored"), plain);
        // The text of another tower's strands, or a key whose source names no strand.
        let text = tower.to_text().replace("strands 2 4 11 ", "strands 2 4 10 ");
        assert!(Tower::from_text(&text).is_err());
        let text = tower.to_text().replace(" 43:3,2,0:p ", " 43:4,2,0:p ");
        assert_ne!(text, tower.to_text());
        assert!(Tower::from_text(&text).is_err());
    }

    /// The strands refuse what they do not carry: a second set, a level past the tower's, no ring,
    /// a ring without a modulus or with its multiplier at it, bytes out of order or in both tables,
    /// a turn at its modulus, a key naming no strand, a word missing, and a stream rested before
    /// the join. The comparison opens on joined strands only, under the pair law, on two strands
    /// each signed `±1`, with four contacts a ring. Beside them the credit and the input covectors
    /// are read as without them (the faces are an input with no covector).
    #[test]
    fn the_strands_refuse_what_they_do_not_carry() {
        let mut tower = stranded(rotor_on(tiny_shaped(2, 11, false, false, false, ContactLaw::Rectifying)), false);
        let d = tower.declaration;
        assert!(tower.join_strands(tiny_strands(&d, 0)).is_err());
        let words = || vec![b"1".to_vec(), b"2".to_vec(), b"+".to_vec(), b"=".to_vec()];
        let ring = |modulus: u32, multiplier: u32| vec![StrandRing { modulus, multiplier }];
        let digit = |b: u8, t: u32| vec![(b, vec![t])];
        let key = |b: u8, source: [i8; 3]| vec![(b, StrandKey { source, sheet: Sheet::Kept })];
        let laws = [StrandLaw::Held, StrandLaw::Stepped, StrandLaw::Turned];
        let refused = |level: usize, rings: Vec<StrandRing>, digits: Vec<(u8, Vec<u32>)>, keys: Vec<(u8, StrandKey)>| Strands::new(&d, level, rings, laws, digits, keys, words()).is_err();
        assert!(!refused(1, ring(11, 10), digit(b'1', 1), key(b'+', [3, 2, 0])));
        assert!(refused(2, ring(11, 10), Vec::new(), Vec::new()));
        assert!(refused(0, Vec::new(), Vec::new(), Vec::new()));
        assert!(refused(0, ring(1, 0), Vec::new(), Vec::new()));
        assert!(refused(0, ring(11, 11), Vec::new(), Vec::new()));
        assert!(refused(0, ring(11, 10), vec![(b'2', vec![2]), (b'1', vec![1])], Vec::new()));
        assert!(refused(0, ring(11, 10), digit(b'+', 1), key(b'+', [3, 2, 0])));
        assert!(refused(0, ring(11, 10), digit(b'1', 11), Vec::new()));
        assert!(refused(0, ring(11, 10), Vec::new(), key(b'+', [4, 2, 0])));
        assert!(Strands::new(&d, 0, ring(11, 10), laws, Vec::new(), Vec::new(), words()[1..].to_vec()).is_err());
        // A stream rested before the join carries no residues.
        let bare = tiny_shaped(2, 11, false, false, false, ContactLaw::Rectifying);
        assert!(tower.advance(&mut bare.rest(), 0).is_err());
        // The comparison.
        assert!(tower.open_strands_comparison([2, 1], [1, -1]).is_err());
        let mut pair = tiny_contacts(2, 9, 8, false, false, false, ContactLaw::Pair);
        assert!(pair.open_strands_comparison([2, 1], [1, -1]).is_err());
        let mut narrow = tiny_contacts(2, 9, 7, false, false, false, ContactLaw::Pair);
        narrow.join_strands(tiny_strands(&narrow.declaration, 1)).expect("joined");
        assert!(narrow.open_strands_comparison([2, 1], [1, -1]).is_err());
        pair.join_strands(tiny_strands(&pair.declaration, 1)).expect("joined");
        for (compared, signs) in [([2, 2], [1, -1]), ([3, 1], [1, -1]), ([2, 1], [2, -1]), ([2, 1], [1, 0])] {
            assert!(pair.clone().open_strands_comparison(compared, signs).is_err(), "{compared:?} {signs:?}");
        }
        assert!(pair.open_strands_comparison([2, 1], [1, -1]).is_ok());
        // The credit and the input covectors are read beside the strands.
        let opening = pair.rest_with_credit();
        let mut s = opening.clone();
        let classes = [0usize, 1, 2, 3];
        let reaches = pair.reaches();
        let cells = pair.forward(&mut s, &classes, &reaches).expect("forward");
        assert!(pair.reverse(&opening, &cells, &classes, None).is_ok());
        let mut credit = opening.credit.clone().expect("credit");
        assert!(pair.advance_credit(&mut credit, &opening, &cells, &reaches).is_ok());
        assert!(pair.read_input_covectors(&mut pair.rest(), &classes, 2, |_| Ok(())).is_ok());
    }

    /// Joined at zero, the strands' material's covector and every other family's match the code
    /// difference on the tower over the passage of 37 classes, read through pair contacts, at steps
    /// of `2^(−12)` units: its twin without strands reads its first level's moves there and not at
    /// `2^(−10)` or `2^(−11)` units, with the rotor at none of the three (measured October 27).
    #[test]
    fn the_strands_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(stranded(tiny_contacts(2, 9, 4, false, false, false, ContactLaw::Pair), false), false, &classes, 12);
    }

    /// The pumped rotor tower with the strands, read at steps of `2^(−8)` units as the pumped rotor
    /// tower is.
    #[test]
    fn the_pumped_strands_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(stranded(rotor_on(tiny_shaped(2, 11, true, true, true, ContactLaw::Rectifying)), false), true, &classes, 8);
    }

    /// The tower opened on the strands' comparison, at steps of `2^(−11)` units: the opened
    /// contacts' covector reaches their strands' material.
    #[test]
    fn the_opened_strands_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(stranded(tiny_contacts(2, 9, 8, false, false, false, ContactLaw::Pair), true), false, &classes, 11);
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

    /// Mode by mode, the bilinear weight sums to the rungs' read, each drive's weight on a mode is
    /// its block's row or column sum over the other drive's weights per contact, and a mode the
    /// read takes nothing of carries no weight in either drive.
    #[test]
    fn the_bilinear_weight_mode_by_mode_sums_to_the_rungs() {
        let declaration = TowerDeclaration { alphabet: 4, width: 4, modes: 16, contacts: 4, levels: 1, gated: false, turned: false, pumped: false, contact: ContactLaw::Pair };
        let mut tower = Tower::found(declaration, &keys(16384)).expect("founded");
        let lv = tower.layout.levels[0].clone();
        let (contact, pair) = (tower.theta[lv.contact..lv.contact + 16].to_vec(), lv.pair);
        tower.theta[pair..pair + 16].copy_from_slice(&contact);
        for i in 0..4 {
            tower.theta[lv.read_re + i * 16 + 5] = 0;
            tower.theta[lv.read_im + i * 16 + 5] = 0;
        }
        let zero = BigUint::from(0u32);
        let modes = &tower.bilinear_modes().expect("read")[0];
        let rungs = &tower.bilinear_rungs().expect("read")[0];
        let rung = |k: usize| (k / turn_ladder(16)).min(MARGIN as usize - 1);
        for (s, row) in rungs.iter().enumerate() {
            for (s2, e) in row.iter().enumerate() {
                let sum: BigUint = (0..16).filter(|&k| rung(k) == s).flat_map(|k| (0..16).filter(move |&k2| rung(k2) == s2).map(move |k2| (k, k2))).map(|(k, k2)| modes.block[k][k2].clone()).sum();
                assert_eq!(&sum, e);
            }
        }
        // The two drives read the same material, so their weights and the block are symmetric.
        assert_eq!(modes.first, modes.second);
        assert!((0..16).all(|k| (0..16).all(|k2| modes.block[k][k2] == modes.block[k2][k])));
        assert_eq!(modes.first[5], zero);
        assert!((0..16).all(|k| modes.block[5][k] == zero && modes.block[k][5] == zero));
        assert!((0..16).filter(|&k| k != 5).all(|k| modes.first[k] > zero && modes.block[k][k] > zero));
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

    /// The tiny tower's pair face: two forms whose weights are read off the fixture's keys, released
    /// so that their values sit near the face's unit.
    fn tiny_pair_face(tower: &Tower) -> PairFace {
        let d = &tower.declaration;
        let hat = d.width + 1;
        let k = keys(16384);
        let forms: Vec<Vec<i64>> = (0..2).map(|v| (0..hat * hat).map(|j| (k[3000 + v * hat * hat + j] as i64) - 128).collect()).collect();
        let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let shifts = forms
            .iter()
            .map(|w| {
                let top = PairFace::exact_values(d.alphabet, d.width, &opening, w).iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
                (128 - top.leading_zeros() as i32 - FACE_BITS as i32).max(0)
            })
            .collect();
        PairFace::new(d.alphabet, d.width, opening, forms, shifts).expect("a pair face")
    }

    /// The tiny tower with pair contacts and its pair face joined, its readout and lift opened
    /// away from zero so they carry a covector.
    fn tiny_pair_faced(levels: usize, gated: bool) -> Tower {
        let mut tower = tiny_declared(levels, gated, false, false, ContactLaw::Pair);
        let face = tiny_pair_face(&tower);
        tower.join_pair_face(face).expect("joined");
        let k = keys(16384);
        let (pr, pe) = (tower.layout.pair_readout, tower.layout.pair_encoding);
        for (j, v) in tower.theta[pr..pe + 8].iter_mut().enumerate() {
            *v = (i32::from_be_bytes([k[4 * j + 8000], k[4 * j + 8001], k[4 * j + 8002], k[4 * j + 8003]]) >> 8) / 4;
        }
        tower
    }

    /// A pair face opens with its readout and lift at zero, so the joined tower reads every passage
    /// exactly as the tower alone; and the face's values are its forms' at the founding encoding.
    #[test]
    fn a_pair_faced_tower_opens_on_itself() {
        let tower = tiny_of(true);
        let mut joined = tower.clone();
        let face = tiny_pair_face(&tower);
        let hat = tower.declaration.width + 1;
        let exact = PairFace::exact_values(4, 4, &face.opening, &face.forms[1]);
        for (prev, cur) in [(4usize, 0usize), (2, 3), (0, 0)] {
            assert_eq!(face.at(prev, cur)[1] as i128, shifted(exact[prev * 4 + cur], face.shifts[1]).expect("released"));
        }
        assert!(face.values.iter().any(|&v| v.unsigned_abs() > 1 << 12), "the fixture's forms read near the unit");
        assert_eq!(face.forms[0].len(), hat * hat);
        joined.join_pair_face(face.clone()).expect("joined");
        assert!(joined.join_pair_face(face).is_err());
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let mut s = tower.rest();
        let mut t = joined.rest();
        assert_eq!(tower.read_cells(&mut s, &classes).expect("read"), joined.read_cells(&mut t, &classes).expect("read"));
        assert_eq!(s, t);
    }

    /// A pair-faced tower and its learner restore exactly from their text.
    #[test]
    fn a_pair_faced_tower_restores_exactly() {
        let tower = tiny_pair_faced(2, true);
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let mut learner = TowerLearner::new(tiny_of(true), 6);
        let seq: Vec<usize> = (0..17).map(|i| i % 4).collect();
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let face = tiny_pair_face(&learner.tower);
        learner.join_pair_face(face).expect("joined");
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let restored = TowerLearner::from_text(&learner.to_text()).expect("restored");
        assert_eq!(restored.tower, learner.tower);
        assert_eq!(restored.to_text(), learner.to_text());
    }

    /// The pair face's readout and lift take the code's difference as their covector.
    #[test]
    fn the_pair_faces_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_pair_faced(2, false), false, &PASSAGE, 10);
        the_covector_of_tower_matches_the_code_difference(tiny_pair_faced(2, true), true, &PASSAGE, 10);
    }

    /// The tiny tower's ring face: one rank riding the first level's second mode, its factors read
    /// off the fixture's keys, each factor released below `2^20` on the fixture. The keys are those
    /// whose ring stays loud over the pumped fixture's passage (its quietest read a fifth of its
    /// loudest): a face is a ratio to its own power, so a ring passing near zero turns its face
    /// steeply, and the keys first read (from `5000`) passed within `1/173` of the loudest and bent
    /// the code over the covector test's steps.
    fn tiny_ring_rank(tower: &Tower) -> RingRank {
        tiny_ring_rank_at(tower, 7000)
    }

    /// A rank whose factors are read from the keys at `at`.
    fn tiny_ring_rank_at(tower: &Tower, at: usize) -> RingRank {
        let d = &tower.declaration;
        let (dims, hat) = (2 * d.modes, d.width + 1);
        let k = keys(16384);
        let w = |from: usize, n: usize| -> Vec<i64> { (0..n).map(|j| k[at + from + j] as i64 - 128).collect() };
        RingRank { a: [w(0, dims), w(100, dims)], b: [w(200, hat), w(300, hat)], g: w(400, dims + 1), release: [8, 8, 8], push_shift: 24, read_shift: 0 }
    }

    fn tiny_ring_face(tower: &Tower) -> RingFace {
        let d = &tower.declaration;
        let opening = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        RingFace::new(d, 0, 1, vec![tiny_ring_rank(tower)], opening, Vec::new()).expect("a ring face")
    }

    /// The tiny tower with its ring face joined and its readout opened away from zero.
    fn tiny_ring_faced(tower: Tower) -> Tower {
        tiny_harmonic_faced(tower, 1)
    }

    /// The tiny tower with its ring face joined, read through `harmonics` characters of its turn,
    /// and its readout opened away from zero.
    fn tiny_harmonic_faced(tower: Tower, harmonics: usize) -> Tower {
        let face = tiny_ring_face(&tower).with_harmonics(harmonics).expect("harmonics");
        tiny_faced_with(tower, face)
    }

    /// The tiny tower with `face` joined and its readout opened away from zero.
    fn tiny_faced_with(tower: Tower, face: RingFace) -> Tower {
        let mut tower = tower;
        tower.join_ring_face(face).expect("joined");
        let k = keys(16384);
        let rr = tower.layout.ring_readout;
        let channels = tower.ring_face().expect("joined").channels(tower.declaration.width);
        for (j, v) in tower.theta[rr..rr + channels * tower.declaration.alphabet].iter_mut().enumerate() {
            *v = (i32::from_be_bytes([k[4 * j + 9000], k[4 * j + 9001], k[4 * j + 9002], k[4 * j + 9003]]) >> 8) / 4;
        }
        tower
    }

    /// A section that holds the material the ring reads deposits elsewhere and leaves the ring's
    /// level carrying every passage exactly as before, so the face the ring pushes from: the ring
    /// then differs from the founded one only through its own factors, which deposit.
    #[test]
    fn a_section_holding_what_the_ring_reads_leaves_its_level_as_it_was() {
        let tower = tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair));
        let a: Vec<usize> = (0..13).map(|i| PASSAGE[i % 13]).collect();
        let b: Vec<usize> = (0..13).map(|i| PASSAGE[(5 * i + 3) % 13]).collect();
        let mut learner = TowerLearner::new(tower.clone(), 6);
        learner.held = tower.ring_read_families();
        let mut states = vec![tower.rest(); 2];
        let receipt = learner.section(&mut states, &[&a, &b]).expect("section");
        assert!(receipt.deposited, "the section deposits outside the hold");
        assert_ne!(learner.tower.theta, tower.theta);
        for family in tower.ring_read_families() {
            assert_eq!(learner.tower.theta[family.clone()], tower.theta[family]);
        }
        let factors = tower.ring_factor_family().expect("a ring-faced tower");
        assert_ne!(learner.tower.theta[factors.clone()], tower.theta[factors.clone()], "the factors deposit");
        let mut refactored = tower.clone();
        refactored.theta[factors.clone()].copy_from_slice(&learner.tower.theta[factors]);
        for passage in [&a, &b] {
            let (mut before, mut after, mut both) = (tower.rest(), learner.tower.rest(), refactored.rest());
            tower.read_cells(&mut before, passage).expect("read");
            learner.tower.read_cells(&mut after, passage).expect("read");
            refactored.read_cells(&mut both, passage).expect("read");
            assert_eq!(before.modes[0], after.modes[0]);
            assert_eq!(both.ring, after.ring, "the ring moves only through its factors");
            assert_ne!(before.modes[1], after.modes[1], "the level above the ring's learns");
        }
    }

    /// A founded family's moments open at its passage's section statistics: over one section they
    /// are that section's covector and its square on the deposit's grain, over two the mean
    /// covector and mean square (`second ≥ first²`); every other moment is left as carried, nothing
    /// deposits, and the streams end where a frozen read of the passage leaves them.
    #[test]
    fn a_founded_familys_moments_open_on_its_passage() {
        let tower = tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair));
        let a: Vec<usize> = (0..25).map(|i| PASSAGE[i % 13]).collect();
        let b: Vec<usize> = (0..25).map(|i| PASSAGE[(5 * i + 3) % 13]).collect();
        let sections: Vec<Vec<&[usize]>> = (0..2).map(|k| vec![&a[12 * k..12 * k + 13], &b[12 * k..12 * k + 13]]).collect();
        let family = tower.ring_family().expect("a ring-faced tower");
        // A learner whose moments have not opened refuses: its first section would overwrite them.
        let mut fresh = TowerLearner::new(tower.clone(), 6);
        let mut states = vec![tower.rest(); 2];
        assert!(fresh.open_moments(family.clone(), &mut states, &sections[..1]).is_err());
        assert_eq!(states, vec![tower.rest(); 2]);
        // One section: the covector itself.
        let mut learner = TowerLearner::new(tower.clone(), 6);
        learner.opened = true;
        assert_eq!(learner.open_moments(family.clone(), &mut states, &sections[..1]).expect("opened"), 1);
        let reaches = tower.reaches();
        let mut g = vec![0i128; tower.theta.len()];
        for c in &sections[0] {
            let mut s = tower.rest();
            let cells = tower.forward(&mut s, c, &reaches).expect("forward");
            for (x, y) in g.iter_mut().zip(tower.reverse(&tower.rest(), &cells, c, None).expect("reverse")) {
                *x += y;
            }
        }
        tower.to_step_grain(&mut g);
        tower.to_move_chart(&mut g);
        assert!(family.clone().any(|i| g[i] != 0));
        assert!(tower.ring_factor_family().expect("a ring-faced tower").any(|i| g[i] != 0), "the factors' covector reaches them");
        for i in family.clone() {
            assert_eq!((learner.first[i], learner.second[i]), (g[i], g[i] * g[i]));
        }
        // Two sections: the means, the rest carried, the material and the streams as a frozen read.
        let mut learner = TowerLearner::new(tower.clone(), 6);
        learner.opened = true;
        let mut states = vec![tower.rest(); 2];
        assert_eq!(learner.open_moments(family.clone(), &mut states, &sections).expect("opened"), 2);
        assert_eq!(learner.tower, tower);
        for i in 0..tower.theta.len() {
            if family.contains(&i) {
                assert!(learner.second[i] + 1 >= learner.first[i] * learner.first[i], "entry {i}");
            } else {
                assert_eq!((learner.first[i], learner.second[i]), (0, 0));
            }
        }
        for (state, passage) in states.iter().zip([&a, &b]) {
            let mut read = tower.rest();
            tower.read_cells(&mut read, passage).expect("read");
            assert_eq!(state.modes, read.modes);
            assert_eq!(state.ring, read.ring);
        }
    }

    /// A ring face opens with its readout at zero, so the joined tower codes every passage exactly
    /// as the tower alone and its modes move alike; the ring itself is carried; a second ring is
    /// refused; and each face is its read as a ratio to its power, whatever the read's size.
    #[test]
    fn a_ring_faced_tower_opens_on_itself() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let face = tiny_ring_face(&tower);
        let mut joined = tower.clone();
        joined.join_ring_face(face.clone()).expect("joined");
        assert!(joined.join_ring_face(face).is_err());
        let (mut s, mut t) = (tower.rest(), joined.rest());
        assert_eq!(tower.read_cells(&mut s, &PASSAGE).expect("read"), joined.read_cells(&mut t, &PASSAGE).expect("read"));
        assert_eq!(s.modes, t.modes);
        assert!(t.ring.iter().all(|&(re, im)| re != 0 || im != 0), "{:?}", t.ring);
        let mut largest = 0u64;
        joined
            .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                let (read, rho) = ring.expect("read");
                let size = read.iter().fold(0, |m: u64, v| m.max(v.unsigned_abs()));
                largest = largest.max(size);
                // Σρ² = 2 · 2^32 (the rms of two channels at 2^16), within the ratio's rounding.
                let power: i128 = rho.iter().map(|&v| v as i128 * v as i128).sum();
                assert!(size < 1 << 12 || (power - (1i128 << 33)).abs() < 1 << 25, "a face off its power: {rho:?} from {read:?}");
                Ok(())
            })
            .expect("read");
        assert!(largest > 1 << (FACE_BITS + 4), "the fixture's reads lie past the face's unit: {largest}");
    }

    /// The ring is the founding's: carried by the placement mode's own move and pushed from the
    /// level's carried face before the move and the arriving class, as the input covector reading
    /// (the founding's survey) reports them, by the founded factors, which the material carries on
    /// its own grain without changing a value they push.
    #[test]
    fn the_ring_rides_the_moves_and_faces_the_founding_reads() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let face = tiny_ring_face(&tower);
        let (d, rank) = (&tower.declaration, tiny_ring_rank(&tower));
        let (dims, mv) = (2 * d.modes, 4);
        let mut joined = tower.clone();
        joined.join_ring_face(face).expect("joined");
        let mut h = (0i128, 0i128);
        let mut expected = Vec::new();
        tower
            .read_input_covectors(&mut tower.rest(), &PASSAGE, 5, |cell| {
                let s = &cell.carried[..dims];
                let m = &cell.moves[mv..mv + 4];
                let mut hat: Vec<i64> = tower.encoding(cell.class).iter().map(|&e| e as i64).collect();
                hat.push(1 << FACE_BITS);
                let (alpha, gamma) = rank.state_factors(s);
                let v = rank.push(alpha, rank.pool(&hat), gamma)?;
                let carried = ring_carry([m[0], m[1], m[2], m[3]].map(i128::from), h);
                h = (carried.0 + v.0, carried.1 + v.1);
                expected.push([h.0 as i64, h.1 as i64]);
                Ok(())
            })
            .expect("read");
        let mut read = Vec::new();
        joined
            .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                let r = ring.expect("read").0;
                read.push([r[0], r[1]]);
                Ok(())
            })
            .expect("read");
        assert_eq!(read, expected);
        assert!(expected.iter().any(|m| m[1] != 0), "the fixture's ring turns off the real axis");
    }

    /// The tiny ring face with founded pair moves at the passage's pairs `(0, 2)`, `(2, 1)`, `(1, 3)`,
    /// `(3, 0)` and the start's `(A, 0)`, each passive and each different.
    fn tiny_pair_moved_face(tower: &Tower) -> RingFace {
        let d = &tower.declaration;
        let opening = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let moves = vec![
            (0, 2, [644_245_094, 322_122_547, 107_374_182, -53_687_091]),
            (1, 3, [-214_748_365, 751_619_277, 0, 0]),
            (2, 1, [858_993_459, -107_374_182, -161_061_274, 53_687_091]),
            (3, 0, [0, -966_367_642, 32_212_255, 0]),
            (d.alphabet, 0, [536_870_912, 0, 0, 0]),
        ];
        RingFace::new(d, 0, 1, vec![tiny_ring_rank(tower)], opening, vec![moves]).expect("a ring face")
    }

    /// The tiny ring face with founded pair moves that reflect the ring at `(0, 2)` (`|β| > |λ|`)
    /// and `(2, 0)` (`λ = 0`), turn it at `(1, 3)` and `(3, 1)`, and restart it at `(3, 0)`: on the
    /// passage its hand reverses, returns at the restart and reverses again.
    fn tiny_reflected_face(tower: &Tower) -> RingFace {
        let d = &tower.declaration;
        let opening = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let moves = vec![
            (0, 2, [107_374_182, 0, 644_245_094, 322_122_547]),
            (1, 3, [-214_748_365, 751_619_277, 0, 0]),
            (2, 0, [0, 0, -429_496_730, 751_619_277]),
            (3, 0, [0, 0, 0, 0]),
            (3, 1, [751_619_277, 214_748_365, 0, 0]),
        ];
        RingFace::new(d, 0, 1, vec![tiny_ring_rank(tower)], opening, vec![moves]).expect("a ring face")
    }

    /// A ring that meets a reflection reads in its own hand: `(Re h, −Im h)` from a reflection to
    /// the next reflection or restart, `(Re h, Im h)` elsewhere, the ring itself carried by the
    /// moves as before; the face restores exactly from its text.
    #[test]
    fn a_reflected_ring_reads_in_its_own_hand() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let face = tiny_reflected_face(&tower);
        let (d, rank) = (&tower.declaration, tiny_ring_rank(&tower));
        let (dims, mv) = (2 * d.modes, 4);
        let mut joined = tower.clone();
        joined.join_ring_face(face.clone()).expect("joined");
        let (mut h, mut hand, mut prev) = ((0i128, 0i128), false, d.alphabet);
        let (mut expected, mut hands) = (Vec::new(), Vec::new());
        tower
            .read_input_covectors(&mut tower.rest(), &PASSAGE, 5, |cell| {
                let s = &cell.carried[..dims];
                let mode = [cell.moves[mv], cell.moves[mv + 1], cell.moves[mv + 2], cell.moves[mv + 3]].map(i128::from);
                let m = face.move_at(0, prev, cell.class, mode);
                let mut hat: Vec<i64> = tower.encoding(cell.class).iter().map(|&e| e as i64).collect();
                hat.push(1 << FACE_BITS);
                let (alpha, gamma) = rank.state_factors(s);
                let v = rank.push(alpha, rank.pool(&hat), gamma)?;
                let carried = ring_carry(m, h);
                h = (carried.0 + v.0, carried.1 + v.1);
                hand = hand_after(m, hand);
                expected.push([h.0 as i64, (if hand { -h.1 } else { h.1 }) as i64]);
                hands.push(hand);
                prev = cell.class;
                Ok(())
            })
            .expect("read");
        let mut read = Vec::new();
        joined
            .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                let r = ring.expect("read").0;
                read.push([r[0], r[1]]);
                Ok(())
            })
            .expect("read");
        assert_eq!(read, expected);
        assert!(hands.contains(&true) && hands.contains(&false), "the passage reverses the hand and restores it: {hands:?}");
        assert!(expected.iter().zip(&hands).any(|(e, &o)| o && e[1] != 0), "a reversed hand is read off the real axis");
        assert_eq!(Tower::from_text(&joined.to_text()).expect("restored"), joined);
    }

    /// A move keeps the hand where its determinant `|λ|² − |β|²` is positive, reverses it where
    /// negative, and restarts the ring in the given hand where it is zero.
    #[test]
    fn a_moves_determinant_keeps_reverses_or_restarts_the_hand() {
        let turn = [751_619_277, 214_748_365, 0, 0];
        let reflection = [0, 0, -429_496_730, 751_619_277];
        let leaning = [107_374_182, 0, 644_245_094, 322_122_547];
        for hand in [false, true] {
            assert_eq!(hand_after(turn, hand), hand);
            assert_eq!(hand_after(reflection, hand), !hand);
            assert_eq!(hand_after(leaning, hand), !hand);
            assert!(!hand_after([0; 4], hand));
            assert!(!hand_after([3, 4, 0, 5], hand), "|λ| = |β|: the move collapses the ring onto a line");
        }
    }

    /// Where the ring rides reflecting pair moves and reads in its own hand, every family's
    /// covector still carries its path.
    #[test]
    fn the_reflected_ring_faces_covector_matches_the_code_difference() {
        let mut tower = tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair));
        let face = tiny_reflected_face(&tower);
        tower.ring.as_mut().expect("joined").moves = face.moves;
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tower, true, &classes, 9);
    }

    /// A ring restarted at a class re-bases into the hand it reads wherever that class arrives on
    /// a reversed hand: its read there is unchanged, and the turns after it count with the restored
    /// hand. Every class of the passage is tried as the restart, at least one restart is met, the
    /// face restores exactly from its text, and a restart outside the alphabet is refused by the
    /// join and by the text.
    #[test]
    fn a_restarted_ring_rebases_into_the_hand_it_reads() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let (d, rank) = (&tower.declaration, tiny_ring_rank(&tower));
        let (dims, mv) = (2 * d.modes, 4);
        let mut met = 0;
        for restart in 0..d.alphabet {
            let face = tiny_reflected_face(&tower).with_restarts(vec![Some(restart)]).expect("restarts");
            let mut joined = tower.clone();
            joined.join_ring_face(face.clone()).expect("joined");
            let (mut h, mut hand, mut prev) = ((0i128, 0i128), false, d.alphabet);
            let mut expected = Vec::new();
            tower
                .read_input_covectors(&mut tower.rest(), &PASSAGE, 5, |cell| {
                    let s = &cell.carried[..dims];
                    let mode = [cell.moves[mv], cell.moves[mv + 1], cell.moves[mv + 2], cell.moves[mv + 3]].map(i128::from);
                    let m = face.move_at(0, prev, cell.class, mode);
                    let mut hat: Vec<i64> = tower.encoding(cell.class).iter().map(|&e| e as i64).collect();
                    hat.push(1 << FACE_BITS);
                    let (alpha, gamma) = rank.state_factors(s);
                    let v = rank.push(alpha, rank.pool(&hat), gamma)?;
                    let carried = ring_carry(m, h);
                    h = (carried.0 + v.0, carried.1 + v.1);
                    hand = hand_after(m, hand);
                    expected.push([h.0 as i64, (if hand { -h.1 } else { h.1 }) as i64]);
                    if hand && cell.class == restart {
                        h = (h.0, -h.1);
                        hand = false;
                        met += 1;
                    }
                    prev = cell.class;
                    Ok(())
                })
                .expect("read");
            let mut read = Vec::new();
            joined
                .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                    let r = ring.expect("read").0;
                    read.push([r[0], r[1]]);
                    Ok(())
                })
                .expect("read");
            assert_eq!(read, expected, "restart at {restart}");
            assert_eq!(Tower::from_text(&joined.to_text()).expect("restored"), joined);
        }
        assert!(met > 0, "the passage meets a restart on a reversed hand");
        let outside = tiny_reflected_face(&tower).with_restarts(vec![Some(d.alphabet)]).expect("restarts");
        assert!(tower.clone().join_ring_face(outside).is_err());
        let mut joined = tower.clone();
        joined.join_ring_face(tiny_reflected_face(&tower).with_restarts(vec![Some(1)]).expect("restarts")).expect("joined");
        let text = joined.to_text();
        assert!(text.contains("ring-restarts 1\n"));
        assert!(Tower::from_text(&text.replace("ring-restarts 1\n", &format!("ring-restarts {}\n", d.alphabet))).is_err());
        assert!(Tower::from_text(&text.replace("ring-restarts 1\n", "ring-restarts -\n")).is_err(), "a written line names a restart");
        assert!(tiny_reflected_face(&tower).with_restarts(Vec::new()).is_err());
    }

    /// Where the ring reflects and restarts its hand, every family's covector still carries its
    /// path: the covector arriving from the future is read in the restarted hand.
    #[test]
    fn the_restarted_ring_faces_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        for restart in 0..4 {
            let mut tower = tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair));
            let face = tiny_reflected_face(&tower);
            let ring = tower.ring.as_mut().expect("joined");
            ring.moves = face.moves;
            ring.restarts = vec![Some(restart)];
            the_covector_of_tower_matches_the_code_difference(tower, true, &classes, 9);
        }
    }

    /// A ring face with founded pair moves rides them where the passage meets their pair and its
    /// mode elsewhere, and restores exactly from its text; a boosting pair move is refused.
    #[test]
    fn a_ring_rides_its_pair_moves_and_restores_them() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let rings = |face: RingFace| -> (Tower, Vec<[i64; 2]>) {
            let mut joined = tower.clone();
            joined.join_ring_face(face).expect("joined");
            let mut read = Vec::new();
            joined
                .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                    let r = ring.expect("read").0;
                    read.push([r[0], r[1]]);
                    Ok(())
                })
                .expect("read");
            (joined, read)
        };
        let (_, plain) = rings(tiny_ring_face(&tower));
        let (moved, read) = rings(tiny_pair_moved_face(&tower));
        assert_eq!(read[0], plain[0], "the first cell turns the ring at rest");
        assert_ne!(read, plain, "the pair moves steer the ring");
        assert_eq!(Tower::from_text(&moved.to_text()).expect("restored"), moved);
        let d = &tower.declaration;
        let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let boost = vec![(0, 2, [966_367_642, 0, 161_061_274, 0])];
        assert!(RingFace::new(d, 0, 1, vec![tiny_ring_rank(&tower)], opening, vec![boost]).is_err());
    }

    /// The tiny tower's face of two ranks: the first rides the pair moves of
    /// [`tiny_pair_moved_face`], the second its mode at every cell.
    fn tiny_two_ring_face(tower: &Tower) -> RingFace {
        let d = &tower.declaration;
        let opening = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let moves = tiny_pair_moved_face(tower).pair_moves()[0].clone();
        RingFace::new(d, 0, 1, vec![tiny_ring_rank(tower), tiny_ring_rank_at(tower, 7500)], opening, vec![moves, Vec::new()]).expect("a ring face")
    }

    /// Two rings closed on different keys ride side by side on one mode: each rank rides its own
    /// table (the first its pair moves, the second its mode), reads as it would alone, and the face
    /// restores both tables from its text; a face of two ranks with one table is refused.
    #[test]
    fn two_rings_ride_their_own_moves_side_by_side() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let reads = |face: RingFace| -> (Tower, Vec<Vec<i64>>) {
            let mut joined = tower.clone();
            joined.join_ring_face(face).expect("joined");
            let mut read = Vec::new();
            joined
                .read_ring(&mut joined.rest(), &PASSAGE, |_, _, _, ring| {
                    read.push(ring.expect("read").0.to_vec());
                    Ok(())
                })
                .expect("read");
            (joined, read)
        };
        let (two, both) = reads(tiny_two_ring_face(&tower));
        let (_, moved) = reads(tiny_pair_moved_face(&tower));
        let d = &tower.declaration;
        let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| tower.encoding(u).to_vec()).collect();
        let second = RingFace::new(d, 0, 1, vec![tiny_ring_rank_at(&tower, 7500)], opening.clone(), Vec::new()).expect("a ring face");
        let (_, plain) = reads(second);
        for ((b, m), p) in both.iter().zip(&moved).zip(&plain) {
            assert_eq!(&b[..2], &m[..], "the first rank rides its pair moves as it would alone");
            assert_eq!(&b[2..], &p[..], "the second rank rides its mode as it would alone");
        }
        assert_eq!(Tower::from_text(&two.to_text()).expect("restored"), two);
        let one_table = vec![tiny_pair_moved_face(&tower).pair_moves()[0].clone()];
        assert!(RingFace::new(d, 0, 1, vec![tiny_ring_rank(&tower), tiny_ring_rank_at(&tower, 7500)], opening, one_table).is_err());
    }

    /// Where one rank rides a held pair move and another its mode, the mode's move takes only the
    /// second's covector, and every family's covector still carries its path.
    #[test]
    fn the_two_ring_faces_covector_matches_the_code_difference() {
        let tower = tiny_declared(2, true, true, true, ContactLaw::Pair);
        let face = tiny_two_ring_face(&tower);
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tiny_faced_with(tower, face), true, &classes, 9);
    }

    /// Where the ring rides a held pair move, the mode carries no ring, and every family's covector
    /// still carries its path.
    #[test]
    fn the_pair_moved_ring_faces_covector_matches_the_code_difference() {
        let mut tower = tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair));
        let face = tiny_pair_moved_face(&tower);
        tower.ring.as_mut().expect("joined").moves = face.moves;
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tower, true, &classes, 9);
    }

    /// A turn's harmonics are its powers on the face's grain: a quarter turn read through four
    /// characters returns `i, −1, −i`, and the half-turn and its conjugate land on the real axis.
    #[test]
    fn a_turns_harmonics_are_its_powers() {
        let unit = 1i32 << FACE_BITS;
        assert_eq!(harmonics_of(&[0, unit], 4).expect("harmonics"), vec![0, unit, -unit, 0, 0, -unit, unit, 0]);
        assert_eq!(harmonics_of(&[-unit, 0], 3).expect("harmonics"), vec![-unit, 0, unit, 0, -unit, 0]);
        assert_eq!(harmonics_of(&[0, 0], 3).expect("harmonics"), vec![0; 6]);
        // An eighth turn, `46341 ≈ 2^16/√2`: `q_h = |ρ| e^(ihπ/4)` to within eight grains.
        let q = harmonics_of(&[46341, 46341], 8).expect("harmonics");
        let (c, u) = (46341, unit);
        let expected = [(c, c), (0, u), (-c, c), (-u, 0), (-c, -c), (0, -u), (c, -c), (u, 0)];
        for (h, (z, e)) in q.chunks_exact(2).zip(expected).enumerate() {
            assert!((z[0] - e.0).abs() < 8 && (z[1] - e.1).abs() < 8, "harmonic {} is {z:?}", h + 1);
        }
        let face = tiny_ring_face(&tiny_declared(2, true, false, false, ContactLaw::Pair));
        assert!(face.clone().with_harmonics(0).is_err());
        assert_eq!(face.with_harmonics(5).expect("harmonics").harmonics(), 5);
    }

    /// Read through its turn's harmonics, the ring face's covector still matches the code
    /// difference: the readout's, and the state's and move's through the turn's tangent.
    #[test]
    fn the_harmonic_ring_faces_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_harmonic_faced(tiny_declared(2, true, false, false, ContactLaw::Pair), 3), true, &PASSAGE, 10);
    }

    /// A ring face read through its harmonics restores exactly from its text, and refuses a
    /// harmonic count below two in it.
    #[test]
    fn a_harmonic_ring_faced_tower_restores_exactly() {
        let tower = tiny_harmonic_faced(tiny_declared(2, true, false, false, ContactLaw::Pair), 4);
        let text = tower.to_text();
        assert!(text.contains("ring-harmonics 4\n"));
        assert_eq!(Tower::from_text(&text).expect("restored"), tower);
        assert!(Tower::from_text(&text.replace("ring-harmonics 4\n", "ring-harmonics 1\n")).is_err());
        assert_eq!(tower.ring_face().expect("joined").channels(tower.declaration.width), (tower.declaration.width + 1) * 2 * 4);
    }

    /// A ring-faced tower and its learner restore exactly from their text.
    #[test]
    fn a_ring_faced_tower_restores_exactly() {
        let tower = tiny_ring_faced(tiny_declared(2, true, false, false, ContactLaw::Pair));
        assert_eq!(Tower::from_text(&tower.to_text()).expect("restored"), tower);
        let mut learner = TowerLearner::new(tiny_declared(2, true, false, false, ContactLaw::Pair), 6);
        let seq: Vec<usize> = (0..17).map(|i| i % 4).collect();
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        let face = tiny_ring_face(&learner.tower);
        learner.join_ring_face(face).expect("joined");
        let mut states = vec![learner.tower.rest()];
        learner.section(&mut states, &[&seq]).expect("section");
        assert!(learner.tower.theta[learner.tower.layout.ring_readout..].iter().any(|&v| v != 0), "the section's deposit reached the ring's readout");
        let restored = TowerLearner::from_text(&learner.to_text()).expect("restored");
        assert_eq!(restored.tower, learner.tower);
        assert_eq!(restored.to_text(), learner.to_text());
    }

    /// The ring face's readout takes the code's difference as its covector, and so do the state and
    /// the move it rides: their covectors carry the ring's path.
    #[test]
    fn the_ring_faces_covector_matches_the_code_difference() {
        the_covector_of_tower_matches_the_code_difference(tiny_ring_faced(tiny_declared(2, true, false, false, ContactLaw::Pair)), true, &PASSAGE, 10);
    }

    /// On the pumped pair tower (the trained towers' kind) the ring rides a move with a pump, `β ≠ 0`,
    /// and every family's covector still carries its path; read over the pumped fixture's passage.
    #[test]
    fn the_pumped_ring_faces_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tiny_ring_faced(tiny_declared(2, true, true, true, ContactLaw::Pair)), true, &classes, 9);
    }

    /// The class before is carried in the state, so a passage read in two parts, the second from the
    /// first's state, codes as the whole: the pair at the seam is read whole.
    #[test]
    fn the_pair_at_a_seam_is_read_from_the_carried_class() {
        let tower = tiny_pair_faced(2, true);
        let classes = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 0, 3, 1, 0];
        let whole = code(&tower, &classes);
        let mut s = tower.rest();
        let first = tower.read(&mut s, &classes[..7]).expect("read");
        assert_eq!(s.previous, classes[5]);
        let second = tower.read(&mut s, &classes[6..]).expect("read");
        assert_eq!(first + second, whole);
        // The seam's pair is the carried class's: from rest the same part reads the start instead.
        let mut rested = tower.rest();
        assert_ne!(tower.read(&mut rested, &classes[6..]).expect("read"), second);
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

    /// The faces read cell by cell code what `read_cells` codes, and a class's rank is 0 exactly
    /// where no class carries more mass.
    #[test]
    fn the_faces_read_code_the_cells() {
        let tower = tiny_turning(2, true, true, false);
        let classes: Vec<usize> = (0..37).map(|i| [0, 2, 1, 3, 0, 1, 2, 3, 3, 0][i % 10]).collect();
        let codes = tower.read_cells(&mut tower.rest(), &classes).expect("codes");
        let mut read = Vec::new();
        let mut firsts = 0;
        tower
            .read_faces(&mut tower.rest(), &classes, |i, _, face| {
                read.push(face.code(classes[i + 1]));
                let top = *face.masses.iter().max().expect("a class");
                for c in 0..face.masses.len() {
                    assert_eq!(face.rank(c) == 0, face.masses[c] == top);
                }
                firsts += (face.rank(classes[i + 1]) == 0) as usize;
                Ok(())
            })
            .expect("read");
        assert_eq!(read, codes);
        assert!(firsts > 0 && firsts < codes.len());
    }

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

    /// The rotor's reverse carries the mode covector back through the inverse step, and every
    /// covector of the move reads the stepped state: read on the ungated tower, whose moves'
    /// covectors are the products `conj(h') G_h` themselves, over the pumped passage of 37 classes.
    #[test]
    fn the_rotor_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(rotor_on(tiny_shaped(2, 4, false, false, false, ContactLaw::Rectifying)), false, &classes, 10);
    }

    /// The pumped rotor tower, read at steps of `2^(−8)` units. At `2^(−9)` the second level's
    /// gate, whose covectors sit nearest the reading's grain, fitted −58.0 against a covector of
    /// −67.2 (×10⁶) on its largest parameter, at `2^(−8)` −63.3, and at `2^(−10)` and `2^(−11)`
    /// −52.3 and −34.3: the fit drifts with the step, the mark of the faces' release, while the first
    /// level's gate, carried back through both levels' steps, fitted within 3% at `2^(−8)` (measured
    /// October 26; no gate was held on the passage).
    #[test]
    fn the_pumped_rotor_covector_matches_the_code_difference() {
        let classes: Vec<usize> = (0..37).map(|i| (i * 7 + i / 3) % 4).collect();
        the_covector_of_tower_matches_the_code_difference(tiny_rotor(), true, &classes, 8);
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
        let (mut checked, mut gates_checked, mut turns_checked, mut pumps_checked, mut pairs_checked, mut faces_checked, mut rings_checked, mut strands_checked) = (0, 0, 0, 0, 0, 0, 0, 0);
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
                faces_checked += (tower.pair.is_some() && (start == tower.layout.pair_readout || start == tower.layout.pair_encoding)) as usize;
                rings_checked += (tower.ring.is_some() && (start == tower.layout.ring_readout || start == tower.layout.ring_factors)) as usize;
                strands_checked += (tower.strands.is_some() && (start == tower.layout.strand_contact || start == tower.layout.strand_pair)) as usize;
                break;
            }
        }
        // A gated tower's gate material and bias are read at the first level (the second level's
        // gate covectors fall below 1/64 bit a unit on this fixture).
        assert!(!gated || gates_checked >= 2, "only {gates_checked} gate families carried a readable covector");
        assert!(!tower.declaration.turned || turns_checked >= 2, "only {turns_checked} turn families carried a readable covector");
        assert!(!tower.declaration.pumped || pumps_checked >= 4, "only {pumps_checked} pump families carried a readable covector");
        assert!(tower.declaration.contact == ContactLaw::Rectifying || pairs_checked >= 2, "only {pairs_checked} pair families carried a readable covector");
        // The pair readout moves only the readout, past every kink; the pair lift moves the
        // encoding at every cell, so on a tower with a kink (a gate, or rectifying contacts) every
        // step of it crosses one somewhere, and it is read on the kinkless tower.
        let kinked = gated || tower.declaration.contact == ContactLaw::Rectifying;
        assert!(tower.pair.is_none() || faces_checked >= if kinked { 1 } else { 2 }, "only {faces_checked} pair face families carried a readable covector");
        assert!(tower.ring.is_none() || rings_checked == 2, "the ring face's readout and factors carried {rings_checked} readable covectors of 2");
        let strand_families = if tower.declaration.contact == ContactLaw::Rectifying { 1 } else { 2 };
        assert!(tower.strands.is_none() || strands_checked == strand_families, "the strands' material carried {strands_checked} readable covectors of {strand_families}");
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
