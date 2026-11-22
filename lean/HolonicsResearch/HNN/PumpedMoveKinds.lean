import HolonicsResearch.HNN.RingHand
import Holonics.HNN.CarryGate

/-!
# A pumped move's kind: turn, free fall, lock, collapse or flip, and a helix's hand

A pumped mode moves by `h ↦ λ h + β·conj(h)` (the October tower's `ring_carry`, whose hand
`HolonicsResearch.HNN.RingHand` proves; the November engine's pumped carry circle
`Q ↦ γ Q + η conj(Q) + κ b`, `crates/engine/src/carry.rs`, `carry_gate_pumped`, whose gate
`Holonics.HNN.CarryGate` states). Source record:
`2026-11-22_A_HELIX_CARRIES_TWO_SIGNS_AND_ITS_HAND_IS_THEIR_PRODUCT_A_RING_ALONE_HAS_NONE_THE_MIRROR_CARRIES_ORDER_COMPARISON_AND_STORAGE_AND_A_CHAIN_COMPOSES_WHERE_ITS_CONTACTS_MEET_OPPOSITE_HANDS.md`.

[proved-derived; formal-checked] What is proved.

1. **The move's trace and discriminant** (`trace_handMatrix`, `disc_handMatrix`): the trace is
   `2 Re λ` and `tr² − 4 det = 4 (|β|² − (Im λ)²)`. With `det_handMatrix` (`|λ|² − |β|²`) the
   move's kind is the pump against the turn: it **turns** where `|β| < |Im λ|`
   (`turns_iff`), falls freely (a shear) where they are equal (`free_fall_iff`), and has two real
   axes past it (`real_axes_iff`), a **lock** of the phase to an axis while `|β| < |λ|`, a
   **collapse** onto a line at `|β| = |λ|` and a **flip** of the plane's hand past it
   (`handMatrix_keeps`, `handMatrix_singular`, `handMatrix_reverses` in `RingHand`).
2. **A common positive scale moves no kind** (`handMatrix_ofReal_mul`, `det_scale`,
   `disc_scale`): the leak that divides the turn and the pump alike scales the determinant and the
   discriminant by its square.
3. **The engine's pumped circle** (`pumped_det`, `pumped_disc`, `pumped_flips_iff`,
   `pumped_turns_iff`, `pumped_real_axes_iff`): with `λ = γ̂(q)/(1 + d + n)` and
   `β = p/(1 + d + n)`, `1 + d + n > 0`, the determinant is `(1 − |p|²)/(1 + d + n)²` and the
   discriminant `4 (|p|² − (4q/(4 + q²))²)/(1 + d + n)²`, so the kind is read from the pump's
   chart `p` against the turn's chart `q` alone: a turn where `|p| < 4|q|/(4 + q²)`, a flip where
   `|p| > 1`.
4. **A helix carries two signs** (`hand`, `dyad`, `mirror`, `dyad_keeps_hand`,
   `mirror_flips_hand`, `dyad_is_inverse`, `mirror_ne_step`, `mirror_ne_inverse`,
   `turn_alone_cannot_tell`): a step is a turn `a` with a carry `c`, its hand the sign of `a·c`
   (the reduced pitch's sign). The dyad reverses both and keeps the hand (it is the inverse step:
   the duplex is antiparallel and of one hand); the mirror reverses the turn alone and flips it, and
   is neither the step nor its inverse where the turn and the carry are nonzero. Read on the turn
   alone, the dyad and the mirror are one map.

Limits. The kinds are those of the move on its own; a chain's kind is its product's, and the
moves need not commute. Nothing here says which kind a trained circle takes: that is a reading of
the line's state.

Computational object: the helical pair interaction, read on the carry circle (the winding guide's
helix and its cell holonomy: the turn and its carry, and the reflection that reverses one).

Consumers: the atlas rows `motion.pumped-move-kinds` and `helical.two-signs-hand`; the record's
read of the line's circles.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PumpedMoveKinds

open Complex ComplexConjugate Matrix
open Holonics.HNN.RingHand Holonics.HNN.CarryGate

/-! ## The move's kind -/

/-- [proved-derived; formal-checked] **The move's trace is `2 Re λ`.** -/
theorem trace_handMatrix (l b : ℂ) : (handMatrix l b).trace = 2 * l.re := by
  simp only [handMatrix, Matrix.trace_fin_two_of]
  ring

/-- [proved-derived; formal-checked] **The move's discriminant:** `tr² − 4 det = 4 (|β|² − (Im λ)²)`. -/
theorem disc_handMatrix (l b : ℂ) :
    (handMatrix l b).trace ^ 2 - 4 * (handMatrix l b).det = 4 * (normSq b - l.im ^ 2) := by
  rw [trace_handMatrix, det_handMatrix, normSq_apply, normSq_apply]
  ring

/-- [proved-derived; formal-checked] **The move turns** (complex axes, an elliptic move) exactly
where the pump is under the turn's rate, `|β|² < (Im λ)²`. -/
theorem turns_iff (l b : ℂ) :
    (handMatrix l b).trace ^ 2 < 4 * (handMatrix l b).det ↔ normSq b < l.im ^ 2 := by
  have h := disc_handMatrix l b
  constructor <;> intro hlt <;> nlinarith

/-- [proved-derived; formal-checked] **The move falls freely** (a repeated axis, the parabolic
threshold) exactly where the pump equals the turn's rate. -/
theorem free_fall_iff (l b : ℂ) :
    (handMatrix l b).trace ^ 2 = 4 * (handMatrix l b).det ↔ normSq b = l.im ^ 2 := by
  have h := disc_handMatrix l b
  constructor <;> intro he <;> nlinarith

/-- [proved-derived; formal-checked] **The move has two real axes** (the phase held to an axis, or
past the collapse a flip) exactly where the pump exceeds the turn's rate. -/
theorem real_axes_iff (l b : ℂ) :
    4 * (handMatrix l b).det < (handMatrix l b).trace ^ 2 ↔ l.im ^ 2 < normSq b := by
  have h := disc_handMatrix l b
  constructor <;> intro hlt <;> nlinarith

/-! ## A common scale moves no kind -/

/-- [proved-derived; formal-checked] **A real scale of both parts scales the move.** -/
theorem handMatrix_ofReal_mul (c : ℝ) (l b : ℂ) :
    handMatrix ((c : ℂ) * l) ((c : ℂ) * b) = c • handMatrix l b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [handMatrix] <;> ring

/-- [proved-derived; formal-checked] **The determinant scales by the square.** -/
theorem det_scale (c : ℝ) (l b : ℂ) :
    (handMatrix ((c : ℂ) * l) ((c : ℂ) * b)).det = c ^ 2 * (handMatrix l b).det := by
  rw [det_handMatrix, det_handMatrix, normSq_mul, normSq_mul, normSq_ofReal]
  ring

/-- [proved-derived; formal-checked] **The discriminant scales by the square.** -/
theorem disc_scale (c : ℝ) (l b : ℂ) :
    normSq ((c : ℂ) * b) - ((c : ℂ) * l).im ^ 2 = c ^ 2 * (normSq b - l.im ^ 2) := by
  rw [normSq_mul, normSq_ofReal, Complex.im_ofReal_mul]
  ring

/-! ## The engine's pumped circle -/

/-- [proved-derived; formal-checked] The pumped turn's imaginary part is the turn's over the leak. -/
theorem pumpedTurn_im (q d n : ℝ) :
    (pumpedTurn q d n).im = 4 * q / (4 + q ^ 2) * (1 / (1 + d + n)) := by
  simp only [pumpedTurn, carryTurn, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add]

/-- [proved-derived; formal-checked] **The pumped circle's determinant** is `(1 − |p|²)/(1 + d + n)²`. -/
theorem pumped_det (q d n : ℝ) (p : ℂ) :
    (handMatrix (pumpedTurn q d n) (pump p d n)).det = (1 - normSq p) * (1 / (1 + d + n)) ^ 2 := by
  rw [det_handMatrix, pumpedTurn, pump, normSq_mul, normSq_mul, normSq_ofReal, carryTurn_normSq]
  ring

/-- [proved-derived; formal-checked] **The pumped circle's discriminant** is
`4 (|p|² − (4q/(4 + q²))²)/(1 + d + n)²`. -/
theorem pumped_disc (q d n : ℝ) (p : ℂ) :
    (handMatrix (pumpedTurn q d n) (pump p d n)).trace ^ 2
        - 4 * (handMatrix (pumpedTurn q d n) (pump p d n)).det
      = 4 * (normSq p - (4 * q / (4 + q ^ 2)) ^ 2) * (1 / (1 + d + n)) ^ 2 := by
  rw [disc_handMatrix, pumpedTurn_im, pump, normSq_mul, normSq_ofReal]
  ring

/-- [proved-derived; formal-checked] **The pumped circle flips the hand exactly where `|p| > 1`.** -/
theorem pumped_flips_iff (q d n : ℝ) (p : ℂ) (h : 0 < 1 + d + n) :
    (handMatrix (pumpedTurn q d n) (pump p d n)).det < 0 ↔ 1 < normSq p := by
  rw [pumped_det]
  have hs : 0 < (1 / (1 + d + n)) ^ 2 := by positivity
  constructor
  · intro hlt
    by_contra hp
    push Not at hp
    have : 0 ≤ (1 - normSq p) * (1 / (1 + d + n)) ^ 2 := mul_nonneg (by linarith) hs.le
    linarith
  · intro hp
    exact mul_neg_of_neg_of_pos (by linarith) hs

/-- [proved-derived; formal-checked] **The pumped circle turns exactly where
`|p| < 4|q|/(4 + q²)`.** -/
theorem pumped_turns_iff (q d n : ℝ) (p : ℂ) (h : 0 < 1 + d + n) :
    (handMatrix (pumpedTurn q d n) (pump p d n)).trace ^ 2
        < 4 * (handMatrix (pumpedTurn q d n) (pump p d n)).det
      ↔ normSq p < (4 * q / (4 + q ^ 2)) ^ 2 := by
  have e := pumped_disc q d n p
  have hs : 0 < (1 / (1 + d + n)) ^ 2 := by positivity
  constructor
  · intro hlt
    by_contra hp
    push Not at hp
    have : 0 ≤ 4 * (normSq p - (4 * q / (4 + q ^ 2)) ^ 2) * (1 / (1 + d + n)) ^ 2 :=
      mul_nonneg (by linarith) hs.le
    linarith
  · intro hp
    have : 4 * (normSq p - (4 * q / (4 + q ^ 2)) ^ 2) * (1 / (1 + d + n)) ^ 2 < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hs
    linarith

/-- [proved-derived; formal-checked] **The pumped circle has two real axes exactly where
`|p| > 4|q|/(4 + q²)`.** -/
theorem pumped_real_axes_iff (q d n : ℝ) (p : ℂ) (h : 0 < 1 + d + n) :
    4 * (handMatrix (pumpedTurn q d n) (pump p d n)).det
        < (handMatrix (pumpedTurn q d n) (pump p d n)).trace ^ 2
      ↔ (4 * q / (4 + q ^ 2)) ^ 2 < normSq p := by
  have e := pumped_disc q d n p
  have hs : 0 < (1 / (1 + d + n)) ^ 2 := by positivity
  constructor
  · intro hlt
    by_contra hp
    push Not at hp
    have : 4 * (normSq p - (4 * q / (4 + q ^ 2)) ^ 2) * (1 / (1 + d + n)) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hs.le
    linarith
  · intro hp
    have : 0 < 4 * (normSq p - (4 * q / (4 + q ^ 2)) ^ 2) * (1 / (1 + d + n)) ^ 2 :=
      mul_pos (by linarith) hs
    linarith

/-! ## A helix carries two signs -/

/-- [definition] **A helix's hand** at a step of turn `s.1` and carry `s.2`: the sign of `a·c`,
the reduced pitch's sign. -/
def hand (s : ℝ × ℝ) : ℝ := s.1 * s.2

/-- [definition] **The dyad** reverses the turn and the carry together. -/
def dyad (s : ℝ × ℝ) : ℝ × ℝ := (-s.1, -s.2)

/-- [definition] **The mirror** reverses the turn and keeps the carry. -/
def mirror (s : ℝ × ℝ) : ℝ × ℝ := (-s.1, s.2)

/-- [proved-derived; formal-checked] **The dyad keeps the hand.** -/
theorem dyad_keeps_hand (s : ℝ × ℝ) : hand (dyad s) = hand s := by
  simp [hand, dyad]

/-- [proved-derived; formal-checked] **The mirror flips the hand.** -/
theorem mirror_flips_hand (s : ℝ × ℝ) : hand (mirror s) = -hand s := by
  simp [hand, mirror]

/-- [proved-derived; formal-checked] **The dyad is the inverse step**: the duplex runs the same
helix backward. -/
theorem dyad_is_inverse (s : ℝ × ℝ) : dyad s = -s := by
  ext <;> simp [dyad]

/-- [proved-derived; formal-checked] **The mirror is not the step** where the turn is nonzero. -/
theorem mirror_ne_step (s : ℝ × ℝ) (ha : s.1 ≠ 0) : mirror s ≠ s := by
  intro h
  have h1 := congrArg Prod.fst h
  simp [mirror] at h1
  exact ha (by linarith)

/-- [proved-derived; formal-checked] **The mirror is not the inverse step** where the carry is
nonzero: the heterochiral partner is a different helix. -/
theorem mirror_ne_inverse (s : ℝ × ℝ) (hc : s.2 ≠ 0) : mirror s ≠ -s := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [mirror] at h2
  exact hc (by linarith)

/-- [proved-derived; formal-checked] **Read on the turn alone, the dyad and the mirror are one map**:
a ring that does not carry its carry cannot tell its antiparallel partner from its heterochiral
one. -/
theorem turn_alone_cannot_tell (s : ℝ × ℝ) : (dyad s).1 = (mirror s).1 := by
  simp [dyad, mirror]

end Holonics.HNN.PumpedMoveKinds
