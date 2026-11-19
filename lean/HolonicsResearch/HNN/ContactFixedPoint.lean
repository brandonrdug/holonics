import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# HNN.ContactFixedPoint: two-sided deposition across a contact meets at the matched pair nearest its opening

[definition] The box of #410: "The fixed point of two-sided deposition across a contact, consumed by key
location (from comment c6002755787)", and the part of the box "Continuous keys: loop-closure inference over
continuous configuration spaces (finite menus are done in `HNN/Keys`)" that a menu of linear contacts carries.
The record of October 5 (§J9, "The key is shaped by the lock: a signal records its receivers") reads reception
as changing both participants, `I_C(|H_S⟩, |H_R⟩) = (|H'_S⟩, |H'_R⟩, f_R)`, deposited over aeons on both sides
of a contact, so that lock and key are one pairing `⟨Ȟ|H⟩` and asking which came first is malformed. Its
missing term is this fixed point as a derived statement, with the keys' loop closure as its consumer.

[definition] The setting. The emitter's state `x : X → ℝ` (the key), the receiver's state `y : Y → ℝ` (the
lock), the contact's readings `A : Matrix K X ℝ` and `B : Matrix K Y ℝ`, and an observed offset `c`; the slip
`Δ = Ax − By − c` (`twoSlip`) and the contact's quadrance `Q = ⟨Δ|Δ⟩`. With `z = (x, y)` and `M = [A, −B]`
(`joint`: the slip map `J = [v_a | −v_b]` of `pair.slip-map`), `Δ = Mz − c` and `MᵀΔ = J*Δ = ½ DQ`
(`contact.dq`). Two-sided deposition at rates `α, β` is the descent of `Q` on both sides from the covector that
reached each, `x ← x − αAᵀΔ`, `y ← y + βBᵀΔ` (`twoStep`), which is `z ← z − D Mᵀ(Mz − c)` with
`D = diag(α, β)` (`step_joint`). The general statements are made for any state index `ι`, readings
`M : Matrix κ ι ℝ` and diagonal rates `d : ι → ℝ` (`step`); `G = M D Mᵀ` is the contact's Gram (`gram`), and
`|u|²_(D⁻¹) = Σ uᵢ²/dᵢ` is the inverse-rate weight (`wnorm`, with its pairing `wpair`).

Sources: the box; the record
`research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md` §J9 (its `[open]` missing
term); `HNN/Keys` (its closing paragraph, "Key location for continuous keys is #410's"; `gauge_fix_unique`,
`field_loop_fibre`) and `Compression/Core/Keys` (`fibre`, `fibre_gauge_invariant`, `fibre_eq_orbit`); the atlas
rows `contact.dq`, `pair.slip-map`, `contact.power`, `contact.sheaf-cohomology-index` (a slip glues iff its
class in the cokernel vanishes), `linalg.lattice-cokernel`, `key.consistent-fibre`, `key.gauge-orbit` and
`hnn.gauge-fix-unique`.

What is proved. Items 1 to 5 are the classical facts of least squares and of the preconditioned descent
(Landweber's iteration with a diagonal preconditioner), [proved-standard; formal-checked]; their readings on
the contact and on keys (items 6 and 7) and the witnesses (item 8) are [proved-derived; formal-checked].

1. **Fixed points** (`isFixed_iff_normal`, `normal_iff_minimizes`, `isFixed_iff_minimizes`,
   `normal_iff_matched`). With every rate nonzero, `z` is fixed iff `Mᵀ(Mz − c) = 0` iff `z` minimizes `Q`;
   when a matched pair exists (`c ∈ range M`) the fixed points are the matched pairs, `Δ = 0`.
2. **The cokernel residual** (`slip_eq_of_normal`, `residual_cokernel`, `residual_unique`,
   `quadrance_eq_residual_add`, `residual_persists`). Every fixed point has the same slip `Δ*`. It is
   orthogonal to `range M` with `c + Δ* ∈ range M`, which characterizes it: `Δ* = −P⊥c`. Every state's
   quadrance is `|Δ*|² + |M(z − z*)|²`, and every state's slip has the component `|Δ*|²` along `Δ*`: no
   deposition on either side removes it.
3. **Descent** (`slip_step`, `gram_sq_le`, `dot_gram_le`, `quadrance_step_le`, `decrement_eq`, `decrement_pos`,
   `quadrance_step_lt`). The slip moves by `Δ⁺ = Δ − GΔ`. Under the step bound `|M(Dv)|² ≤ ⟨v, Dv⟩` for every
   `v` (`StepBound`, which says `‖M D^(1/2)‖ ≤ 1`), `Q(z⁺) ≤ Q(z) − ⟨MᵀΔ, D MᵀΔ⟩`; with positive rates the
   decrease is strict away from a fixed point.
4. **Conservation and the meeting point** (`wpair_step`, `iterate_moving`, `IsMeeting`, `meeting_pythagoras`,
   `meeting_nearest`, `meeting_unique`, `ker_normal_gram`, `exists_meeting`, `equal_rates_nearest`). For every
   gauge direction `h ∈ ker M` the pairing `⟨h, z⟩_(D⁻¹)` is conserved by every step, because the step moves
   `z` only along `D range Mᵀ`, and the iterates stay in `z₀ + D range Mᵀ`. The fixed point in that set (the
   meeting point) exists in finite dimension (`ker(MᵀG) = ker Mᵀ`, so by rank–nullity
   `range(MᵀG) = range Mᵀ`), it is unique, and it is the `D⁻¹`-nearest fixed point to `z₀`, by a Pythagoras in
   the `D⁻¹` weight; with equal rates it is the nearest in the plain dot product.
5. **Convergence** (`Gap`, `exists_gap`, `contraction`, `iterate_contracts`, `converges_geometric`,
   `slip_converges`, `tendsto_meeting`, `tendsto_meeting'`, `limit_eq_meeting`). The spectral gap
   `μ⟨w, Gw⟩ ≤ |Gw|²` with `0 < μ ≤ 1` (on the moving directions `u = D Mᵀw`, the slip `|Mu|²` is at least
   `μ|u|²_(D⁻¹)`) holds for some `μ` whenever the rates are positive, by compactness of the moving directions'
   weighted unit sphere. Under it and the step bound, `|z_t − z*|²_(D⁻¹) ≤ (1 − μ)^t |z₀ − z*|²_(D⁻¹)` and
   `|Δ_t − Δ*|²` obeys the same bound, so the iterates converge to the meeting point `z*`, and any limit is it.
6. **The two-sided reading** (`twoSlip`, `twoStep`, `joint`, `rates`, `slip_joint`, `joint_transpose_mulVec`,
   `step_joint`, `twoSlip_step`, `twoStep_fixed_iff`, `rates_moving_joint`, `scalar_bound`, `stepBound_joint`,
   `twoStep_conserves`, `twoStep_rate_zero`, `twoStep_swap`). The joint step is the pair of side updates; one
   step lowers the slip by `αA AᵀΔ + βB BᵀΔ`; a pair is fixed iff both sides' covectors `AᵀΔ` and `BᵀΔ`
   vanish. The bound `α‖A‖² + β‖B‖² ≤ 1` (stated as `|Av|² ≤ a|v|²`, `|Bv|² ≤ b|v|²`, `αa + βb ≤ 1`) gives the
   step bound. `β⟨h_x, x⟩ + α⟨h_y, y⟩` is conserved for every gauge pair `A h_x = B h_y` at every pair of
   rates, zero included. With `β = 0` the lock does not move and the key's step is the one-sided step with the
   lock's reading folded into the offset. Exchanging the roles, `(A, x, α) ↔ (B, y, β)` with `c ↦ −c`,
   exchanges the two updates: the law names no first side. With equal rates `r` the two sides move by their
   shares `(rAᵀw, −rBᵀw)` of one covector `w`, to the nearest fixed point in the plain dot product.
7. **Key location, continuous keys** (`keys`, `keys_gauge_invariant`, `keys_eq_orbit`, `mem_keys_iff_isFixed`,
   `gauge_fix_unique`, `deposition_locates_key`). A menu of linear contacts is one `M` and `c` (rows stacked);
   the keys are the fibre `{z | Mz = c}` of the closure map. It is a union of gauge orbits under `ker M` (the
   counterpart of `Keys.fibre_gauge_invariant`) and, when nonempty, one orbit (of `Keys.fibre_eq_orbit`); with
   a matched pair the keys are the fixed points of deposition. Relative to an opening `z₀` a single key has zero
   gauge component, `⟨h, z − z₀⟩_(D⁻¹) = 0` for every `h ∈ ker M` (the counterpart of
   `HNN/Keys.gauge_fix_unique`), and two-sided deposition from `z₀` converges to it, the `D⁻¹`-nearest key:
   the gauge is fixed by the opening.
8. **The scalar witness** (`one₁`, `witness_equal_rates`, `witness_stepBound`, `witness_meeting`,
   `witness_key_alone`, `witness_residual`). `A = B = 1`, `c = 0`: from `(x, y) = (1, 0)` at `α = β = ½` one
   step reaches `(½, ½)`, matched, the midpoint, which is the meeting point, and these rates hold the step
   bound. At `α = 1, β = 0` one step reaches `(0, 0)`, and at `α = ½, β = 0` it reaches `(½, 0)` with slip `½`:
   the key alone moves. The contact `A = (1, 1)ᵀ`, `B = 0`, `c = (0, 2)` is fixed at `(x, y) = (1, 0)` at
   every pair of rates, with slip `(1, −1)`, the cokernel residual.

What is not claimed. Nonlinear readings (the helical pair's `Δ = x_a(s) − x_b(t)` on curved strands; here the
readings are linear), noise in the observed offset, the rotor (discrete) case (`HNN/Keys`,
`Compression/Core/Keys`), and a law for the rates: `α, β` are given, the step bound is a hypothesis, and the
gap `μ` is located by compactness, never computed. The statements are over `ℝ`; the precision law's declared
widths, releases and remainders are not modeled. The convergence statements take every rate positive;
one-sided deposition enters them through `twoStep_rate_zero`, as the general statements on the key alone. No
parity ties these statements to the Rust owner `hnn::keys`, and nothing here says that the machine's
deposition is this linear law.

The computational object is the helical pair interaction read on one contact: the slip `Δ` is the contact's
separation, `Q = ⟨Δ|Δ⟩` its quadrance, `M = [A, −B]` its slip map and `MᵀΔ` the first variation `½DQ`, split
into the covector that reaches the key (`AᵀΔ`) and the one that reaches the lock (`−BᵀΔ`); deposition is a
dissipative descent of `Q` (the contact as a resistive element, `contact.power`) on both sides at once. Of the
winding guide's six general objects this touches the pair (the contact, its slip map and its two-sided
deposit) and faces and placement (the fibre of keys, its gauge and the key the opening places); the helix,
the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ContactFixedPoint

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-! ## 1. The contact, its slip and its two-sided step -/

/-- [definition] **The slip** `Δ = Mz − c` of a state `z` across the contact's readings `M`. -/
def slip (M : Matrix κ ι ℝ) (c : κ → ℝ) (z : ι → ℝ) : κ → ℝ := M *ᵥ z - c

/-- [definition] **The contact's quadrance** `Q = ⟨Δ|Δ⟩`. -/
def quadrance (M : Matrix κ ι ℝ) (c : κ → ℝ) (z : ι → ℝ) : ℝ := slip M c z ⬝ᵥ slip M c z

/-- [definition] **The deposition step** `z ← z − D Mᵀ(Mz − c)` at the diagonal rates `d`. -/
def step (M : Matrix κ ι ℝ) (c : κ → ℝ) (d z : ι → ℝ) : ι → ℝ :=
  z - d * (Mᵀ *ᵥ slip M c z)

/-- [definition] **The contact's Gram** `G w = M D Mᵀ w`. -/
def gram (M : Matrix κ ι ℝ) (d : ι → ℝ) (w : κ → ℝ) : κ → ℝ := M *ᵥ (d * (Mᵀ *ᵥ w))

/-- [definition] A state the step leaves where it is. -/
def IsFixed (M : Matrix κ ι ℝ) (c : κ → ℝ) (d z : ι → ℝ) : Prop := step M c d z = z

/-- [definition] **The normal equations** `Mᵀ(Mz − c) = 0`. -/
def Normal (M : Matrix κ ι ℝ) (c : κ → ℝ) (z : ι → ℝ) : Prop := Mᵀ *ᵥ slip M c z = 0

/-- [definition] **The step bound** `|M(Dv)|² ≤ ⟨v, Dv⟩` for every `v`, that is `‖M D^(1/2)‖ ≤ 1`. -/
def StepBound (M : Matrix κ ι ℝ) (d : ι → ℝ) : Prop :=
  ∀ v : ι → ℝ, M *ᵥ (d * v) ⬝ᵥ M *ᵥ (d * v) ≤ v ⬝ᵥ (d * v)

/-- [definition] **The inverse-rate weight** `|u|²_(D⁻¹) = Σ uᵢ²/dᵢ`. -/
noncomputable def wnorm (d u : ι → ℝ) : ℝ := ∑ i, u i ^ 2 / d i

/-- [definition] Its pairing `⟨u, v⟩_(D⁻¹) = Σ uᵢvᵢ/dᵢ`. -/
noncomputable def wpair (d u v : ι → ℝ) : ℝ := ∑ i, u i * v i / d i

/-- [proved-standard; formal-checked] A real dot square is nonnegative. -/
theorem dot_self_nonneg {σ : Type*} [Fintype σ] (v : σ → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- [proved-standard; formal-checked] The adjoint: `⟨w, Mv⟩ = ⟨Mᵀw, v⟩`. -/
theorem dot_mulVec (M : Matrix κ ι ℝ) (w : κ → ℝ) (v : ι → ℝ) :
    w ⬝ᵥ M *ᵥ v = Mᵀ *ᵥ w ⬝ᵥ v := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- [proved-standard; formal-checked] The adjoint read the other way: `⟨u, Mᵀw⟩ = ⟨Mu, w⟩`. -/
theorem dot_transpose_mulVec (M : Matrix κ ι ℝ) (u : ι → ℝ) (w : κ → ℝ) :
    u ⬝ᵥ Mᵀ *ᵥ w = M *ᵥ u ⬝ᵥ w := by
  rw [dot_mulVec, transpose_transpose]

/-- [proved-standard; formal-checked] A dot product against a rate-weighted vector, termwise. -/
theorem dot_weighted (d u v : ι → ℝ) : u ⬝ᵥ (d * v) = ∑ i, d i * (u i * v i) := by
  simp only [dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

omit [Fintype κ] in
/-- [proved-standard; formal-checked] Two slips differ by the reading of the states' difference. -/
theorem slip_sub (M : Matrix κ ι ℝ) (c : κ → ℝ) (z z' : ι → ℝ) :
    slip M c z - slip M c z' = M *ᵥ (z - z') := by
  simp only [slip, mulVec_sub]; abel

/-- [proved-standard; formal-checked] **One step moves the slip by the Gram:** `Δ⁺ = Δ − GΔ`. -/
theorem slip_step (M : Matrix κ ι ℝ) (c : κ → ℝ) (d z : ι → ℝ) :
    slip M c (step M c d z) = slip M c z - gram M d (slip M c z) := by
  simp only [slip, step, gram, mulVec_sub]
  abel

/-- [proved-standard; formal-checked] `⟨w, Gw⟩ = ⟨Mᵀw, D Mᵀw⟩`. -/
theorem dot_gram (M : Matrix κ ι ℝ) (d : ι → ℝ) (w : κ → ℝ) :
    w ⬝ᵥ gram M d w = Mᵀ *ᵥ w ⬝ᵥ (d * (Mᵀ *ᵥ w)) := by
  rw [gram, dot_mulVec]

/-- [proved-standard; formal-checked] `⟨w, Gw⟩ = Σ dᵢ (Mᵀw)ᵢ²`. -/
theorem dot_gram_eq_sum (M : Matrix κ ι ℝ) (d : ι → ℝ) (w : κ → ℝ) :
    w ⬝ᵥ gram M d w = ∑ i, d i * (Mᵀ *ᵥ w) i ^ 2 := by
  rw [dot_gram, dot_weighted]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] A weighted sum of squares at nonnegative rates is nonnegative. -/
theorem wsq_nonneg {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) (x : ι → ℝ) : 0 ≤ ∑ i, d i * x i ^ 2 :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hd i) (sq_nonneg _)

/-- [proved-standard; formal-checked] At positive rates a weighted sum of squares vanishes only at zero. -/
theorem wsq_eq_zero_iff {d : ι → ℝ} (hd : ∀ i, 0 < d i) (x : ι → ℝ) :
    ∑ i, d i * x i ^ 2 = 0 ↔ x = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (hd i).le (sq_nonneg _)]
  constructor
  · intro h; funext i
    have := h i (Finset.mem_univ i)
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' (hd i).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h'
  · rintro rfl i _; simp

/-- [proved-standard; formal-checked] At nonnegative rates the Gram is positive semidefinite. -/
theorem dot_gram_nonneg {d : ι → ℝ} (hd : ∀ i, 0 ≤ d i) (M : Matrix κ ι ℝ) (w : κ → ℝ) :
    0 ≤ w ⬝ᵥ gram M d w := by
  rw [dot_gram_eq_sum]; exact wsq_nonneg hd _

/-- [proved-standard; formal-checked] Under the step bound, `|Gw|² ≤ ⟨w, Gw⟩`. -/
theorem gram_sq_le {M : Matrix κ ι ℝ} {d : ι → ℝ} (hb : StepBound M d) (w : κ → ℝ) :
    gram M d w ⬝ᵥ gram M d w ≤ w ⬝ᵥ gram M d w := by
  rw [dot_gram]; exact hb _

/-- [proved-standard; formal-checked] Under the step bound, `⟨w, Gw⟩ ≤ |w|²`. -/
theorem dot_gram_le {M : Matrix κ ι ℝ} {d : ι → ℝ} (hb : StepBound M d) (w : κ → ℝ) :
    w ⬝ᵥ gram M d w ≤ w ⬝ᵥ w := by
  have h0 : 0 ≤ (w - gram M d w) ⬝ᵥ (w - gram M d w) := dot_self_nonneg _
  have hs : gram M d w ⬝ᵥ w = w ⬝ᵥ gram M d w := dotProduct_comm _ _
  simp only [sub_dotProduct, dotProduct_sub] at h0
  linarith [gram_sq_le hb w]

/-! ## 2. Fixed points and the cokernel residual -/

variable {M : Matrix κ ι ℝ} {c : κ → ℝ} {d : ι → ℝ}

/-- [proved-standard; formal-checked] **With nonzero rates, fixed iff the normal equations hold.** -/
theorem isFixed_iff_normal (hd : ∀ i, d i ≠ 0) (z : ι → ℝ) :
    IsFixed M c d z ↔ Normal M c z := by
  rw [IsFixed, step, sub_eq_self, Normal]
  constructor
  · intro h; funext i
    have := congrFun h i
    simp only [Pi.mul_apply, Pi.zero_apply] at this
    exact (mul_eq_zero.mp this).resolve_left (hd i)
  · intro h; rw [h, mul_zero]

/-- [proved-standard; formal-checked] `Q(z + h) = Q(z) + 2⟨MᵀΔ, h⟩ + |Mh|²`. -/
theorem quadrance_add (z h : ι → ℝ) :
    quadrance M c (z + h) =
      quadrance M c z + 2 * (Mᵀ *ᵥ slip M c z ⬝ᵥ h) + M *ᵥ h ⬝ᵥ M *ᵥ h := by
  have hs : slip M c (z + h) = slip M c z + M *ᵥ h := by
    simp only [slip, mulVec_add]; abel
  rw [quadrance, quadrance, hs, ← dot_mulVec]
  simp only [add_dotProduct, dotProduct_add, dotProduct_comm (M *ᵥ h) (slip M c z)]
  ring

/-- [proved-standard; formal-checked] **The normal equations hold iff `z` minimizes the quadrance.** -/
theorem normal_iff_minimizes (z : ι → ℝ) :
    Normal M c z ↔ ∀ z', quadrance M c z ≤ quadrance M c z' := by
  constructor
  · intro hz z'
    have := quadrance_add (M := M) (c := c) z (z' - z)
    rw [add_sub_cancel, hz, zero_dotProduct, mul_zero, add_zero] at this
    rw [this]; linarith [dot_self_nonneg (M *ᵥ (z' - z))]
  · intro hmin
    set g := Mᵀ *ᵥ slip M c z with hg
    set a := g ⬝ᵥ g
    set b := M *ᵥ g ⬝ᵥ M *ᵥ g
    have ha : 0 ≤ a := dot_self_nonneg g
    have hb : 0 ≤ b := dot_self_nonneg _
    set t := a / (b + 1)
    have ht : t * (b + 1) = a := div_mul_cancel₀ a (by linarith)
    have h1 := hmin (z + (-t) • g)
    rw [quadrance_add, ← hg, mulVec_smul, dotProduct_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, smul_eq_mul] at h1
    have h2 : t ^ 2 * (b + 2) ≤ 0 := by nlinarith
    have h3 : t = 0 := by
      have : t ^ 2 ≤ 0 := by nlinarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg t))
    have h4 : a = 0 := by rw [← ht, h3, zero_mul]
    exact dotProduct_self_eq_zero.mp h4

/-- [proved-standard; formal-checked] **With nonzero rates, fixed iff a minimizer of the quadrance.** -/
theorem isFixed_iff_minimizes (hd : ∀ i, d i ≠ 0) (z : ι → ℝ) :
    IsFixed M c d z ↔ ∀ z', quadrance M c z ≤ quadrance M c z' :=
  (isFixed_iff_normal hd z).trans (normal_iff_minimizes z)

/-- [proved-standard; formal-checked] **When a matched pair exists, the normal points are the matched pairs.** -/
theorem normal_iff_matched (hc : ∃ z₁, M *ᵥ z₁ = c) (z : ι → ℝ) :
    Normal M c z ↔ slip M c z = 0 := by
  constructor
  · intro hz
    obtain ⟨z₁, rfl⟩ := hc
    have hs : slip M (M *ᵥ z₁) z = M *ᵥ (z - z₁) := by rw [slip, mulVec_sub]
    apply dotProduct_self_eq_zero.mp
    conv_lhs => rw [hs]
    rw [dot_mulVec, ← hs, hz, zero_dotProduct]
  · intro h; rw [Normal, h, mulVec_zero]

/-- [proved-standard; formal-checked] **Every normal point has the same slip.** -/
theorem slip_eq_of_normal {z₁ z₂ : ι → ℝ} (h₁ : Normal M c z₁) (h₂ : Normal M c z₂) :
    slip M c z₁ = slip M c z₂ := by
  rw [← sub_eq_zero]
  apply dotProduct_self_eq_zero.mp
  have e := slip_sub M c z₁ z₂
  calc (slip M c z₁ - slip M c z₂) ⬝ᵥ (slip M c z₁ - slip M c z₂)
      = (slip M c z₁ - slip M c z₂) ⬝ᵥ M *ᵥ (z₁ - z₂) := by rw [← e]
    _ = Mᵀ *ᵥ (slip M c z₁ - slip M c z₂) ⬝ᵥ (z₁ - z₂) := dot_mulVec _ _ _
    _ = 0 := by rw [mulVec_sub, h₁, h₂, sub_zero, zero_dotProduct]

/-- [proved-standard; formal-checked] **The fixed slip is a cokernel residual:** `Δ* ⊥ range M`, `c + Δ* = Mz*`. -/
theorem residual_cokernel {z : ι → ℝ} (hz : Normal M c z) :
    (∀ v, slip M c z ⬝ᵥ M *ᵥ v = 0) ∧ c + slip M c z = M *ᵥ z := by
  refine ⟨fun v => by rw [dot_mulVec, hz, zero_dotProduct], ?_⟩
  rw [slip]; abel

/-- [proved-standard; formal-checked] **The residual is characterized:** `r ⊥ range M`, `c + r ∈ range M` ⇒ `r = Δ*`. -/
theorem residual_unique {z : ι → ℝ} (hz : Normal M c z) (r : κ → ℝ)
    (hr : ∀ v, r ⬝ᵥ M *ᵥ v = 0) (hr' : ∃ z', c + r = M *ᵥ z') : r = slip M c z := by
  obtain ⟨z', hz'⟩ := hr'
  have hdiff : r - slip M c z = M *ᵥ (z' - z) := by
    rw [mulVec_sub, ← hz', ← (residual_cokernel hz).2]; abel
  rw [← sub_eq_zero]
  apply dotProduct_self_eq_zero.mp
  calc (r - slip M c z) ⬝ᵥ (r - slip M c z) = (r - slip M c z) ⬝ᵥ M *ᵥ (z' - z) := by rw [← hdiff]
    _ = 0 := by rw [sub_dotProduct, hr, (residual_cokernel hz).1, sub_zero]

/-- [proved-standard; formal-checked] **Pythagoras at a normal point:** `Q(z') = Q(z*) + |M(z' − z*)|²`. -/
theorem quadrance_eq_residual_add {z : ι → ℝ} (hz : Normal M c z) (z' : ι → ℝ) :
    quadrance M c z' = quadrance M c z + M *ᵥ (z' - z) ⬝ᵥ M *ᵥ (z' - z) := by
  have := quadrance_add (M := M) (c := c) z (z' - z)
  rwa [add_sub_cancel, hz, zero_dotProduct, mul_zero, add_zero] at this

/-- [proved-standard; formal-checked] **No deposition removes the residual:** every slip has `⟨Δ, Δ*⟩ = |Δ*|²`. -/
theorem residual_persists {z : ι → ℝ} (hz : Normal M c z) (z' : ι → ℝ) :
    slip M c z' ⬝ᵥ slip M c z = slip M c z ⬝ᵥ slip M c z ∧
      quadrance M c z ≤ quadrance M c z' := by
  refine ⟨?_, ?_⟩
  · have h : slip M c z' = slip M c z + M *ᵥ (z' - z) := by rw [← slip_sub]; abel
    rw [h, add_dotProduct, dotProduct_comm (M *ᵥ (z' - z)), (residual_cokernel hz).1, add_zero]
  · rw [quadrance_eq_residual_add hz z']; linarith [dot_self_nonneg (M *ᵥ (z' - z))]

/-! ## 3. Descent -/

/-- [proved-standard; formal-checked] **Descent:** under the step bound, `Q(z⁺) ≤ Q(z) − ⟨Δ, GΔ⟩`. -/
theorem quadrance_step_le (hb : StepBound M d) (z : ι → ℝ) :
    quadrance M c (step M c d z) ≤
      quadrance M c z - slip M c z ⬝ᵥ gram M d (slip M c z) := by
  rw [quadrance, quadrance, slip_step]
  have := gram_sq_le hb (slip M c z)
  simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (gram M d (slip M c z)) (slip M c z)]
  linarith

/-- [proved-standard; formal-checked] The decrement is `⟨MᵀΔ, D MᵀΔ⟩ = Σ dᵢ (MᵀΔ)ᵢ²`. -/
theorem decrement_eq (z : ι → ℝ) :
    slip M c z ⬝ᵥ gram M d (slip M c z) = ∑ i, d i * (Mᵀ *ᵥ slip M c z) i ^ 2 :=
  dot_gram_eq_sum M d _

/-- [proved-standard; formal-checked] At positive rates the decrement is positive away from a fixed point. -/
theorem decrement_pos (hd : ∀ i, 0 < d i) {z : ι → ℝ} (h : ¬ IsFixed M c d z) :
    0 < slip M c z ⬝ᵥ gram M d (slip M c z) := by
  rw [isFixed_iff_normal (fun i => (hd i).ne'), Normal] at h
  rw [decrement_eq]
  rcases (wsq_nonneg (fun i => (hd i).le) (Mᵀ *ᵥ slip M c z)).eq_or_lt with h0 | h0
  · exact absurd ((wsq_eq_zero_iff hd _).mp h0.symm) h
  · exact h0

/-- [proved-standard; formal-checked] **Strict descent away from a fixed point.** -/
theorem quadrance_step_lt (hd : ∀ i, 0 < d i) (hb : StepBound M d) {z : ι → ℝ}
    (h : ¬ IsFixed M c d z) : quadrance M c (step M c d z) < quadrance M c z := by
  linarith [quadrance_step_le (c := c) hb z, decrement_pos hd h]

/-! ## 4. Conservation and the meeting point -/

/-- [proved-standard; formal-checked] The inverse-rate weight is nonnegative at nonnegative rates. -/
theorem wnorm_nonneg (hd : ∀ i, 0 ≤ d i) (u : ι → ℝ) : 0 ≤ wnorm d u :=
  Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hd i)

/-- [proved-standard; formal-checked] At positive rates the inverse-rate weight vanishes only at zero. -/
theorem wnorm_eq_zero_iff (hd : ∀ i, 0 < d i) (u : ι → ℝ) : wnorm d u = 0 ↔ u = 0 := by
  have h : wnorm d u = ∑ i, (d i)⁻¹ * u i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [h, wsq_eq_zero_iff (fun i => inv_pos.mpr (hd i))]

/-- [proved-standard; formal-checked] `|u + v|²_(D⁻¹) = |u|²_(D⁻¹) + 2⟨u, v⟩_(D⁻¹) + |v|²_(D⁻¹)`. -/
theorem wnorm_add (d u v : ι → ℝ) :
    wnorm d (u + v) = wnorm d u + 2 * wpair d u v + wnorm d v := by
  simp only [wnorm, wpair, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] `|u − v|²_(D⁻¹) = |u|²_(D⁻¹) − 2⟨u, v⟩_(D⁻¹) + |v|²_(D⁻¹)`. -/
theorem wnorm_sub (d u v : ι → ℝ) :
    wnorm d (u - v) = wnorm d u - 2 * wpair d u v + wnorm d v := by
  simp only [wnorm, wpair, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] `|a u|²_(D⁻¹) = a² |u|²_(D⁻¹)`. -/
theorem wnorm_smul (d u : ι → ℝ) (a : ℝ) : wnorm d (a • u) = a ^ 2 * wnorm d u := by
  simp only [wnorm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] The pairing of a vector with itself is its weight. -/
theorem wpair_self (d u : ι → ℝ) : wpair d u u = wnorm d u :=
  Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] The pairing is additive in its second argument. -/
theorem wpair_sub_right (d h u v : ι → ℝ) : wpair d h (u - v) = wpair d h u - wpair d h v := by
  simp only [wpair, ← Finset.sum_sub_distrib, Pi.sub_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- [proved-standard; formal-checked] With nonzero rates, `⟨u, Dv⟩_(D⁻¹) = ⟨u, v⟩`. -/
theorem wpair_weighted (hd : ∀ i, d i ≠ 0) (u v : ι → ℝ) : wpair d u (d * v) = u ⬝ᵥ v := by
  simp only [wpair, dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by have := hd i; field_simp

/-- [proved-standard; formal-checked] A moving direction's weight is the Gram's form: `|D Mᵀw|²_(D⁻¹) = ⟨w, Gw⟩`. -/
theorem wnorm_weighted (w : κ → ℝ) :
    wnorm d (d * (Mᵀ *ᵥ w)) = w ⬝ᵥ gram M d w := by
  rw [dot_gram_eq_sum]
  simp only [wnorm, Pi.mul_apply]
  exact Finset.sum_congr rfl fun i _ => by field_simp

/-- [proved-standard; formal-checked] **Gauge and moving directions are `D⁻¹`-orthogonal:** `⟨h, D Mᵀw⟩_(D⁻¹) = 0`. -/
theorem wpair_gauge_moving (hd : ∀ i, d i ≠ 0) {h : ι → ℝ} (hh : M *ᵥ h = 0) (w : κ → ℝ) :
    wpair d h (d * (Mᵀ *ᵥ w)) = 0 := by
  rw [wpair_weighted hd, dot_transpose_mulVec, hh, zero_dotProduct]

/-- [proved-standard; formal-checked] **Conservation:** every step keeps `⟨h, z⟩_(D⁻¹)` for every `h ∈ ker M`. -/
theorem wpair_step (hd : ∀ i, d i ≠ 0) {h : ι → ℝ} (hh : M *ᵥ h = 0) (z : ι → ℝ) :
    wpair d h (step M c d z) = wpair d h z := by
  rw [step, wpair_sub_right, wpair_gauge_moving hd hh, sub_zero]

/-- [proved-standard; formal-checked] **The iterates move only along `D range Mᵀ`:** `z_t − z₀ = D Mᵀw`. -/
theorem iterate_moving (z₀ : ι → ℝ) (t : ℕ) :
    ∃ w, (step M c d)^[t] z₀ - z₀ = d * (Mᵀ *ᵥ w) := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ t ih =>
      obtain ⟨w, hw⟩ := ih
      refine ⟨w - slip M c ((step M c d)^[t] z₀), ?_⟩
      rw [Function.iterate_succ_apply', step, mulVec_sub, mul_sub, ← hw]
      abel

/-- [definition] **The meeting point** from `z₀`: a normal point in `z₀ + D range Mᵀ`. -/
def IsMeeting (M : Matrix κ ι ℝ) (c : κ → ℝ) (d z₀ z : ι → ℝ) : Prop :=
  Normal M c z ∧ ∃ w, z - z₀ = d * (Mᵀ *ᵥ w)

/-- [proved-standard; formal-checked] **Pythagoras in the `D⁻¹` weight** at the meeting point. -/
theorem meeting_pythagoras (hd : ∀ i, d i ≠ 0) {z₀ z z' : ι → ℝ} (hm : IsMeeting M c d z₀ z)
    (hz' : Normal M c z') : wnorm d (z' - z₀) = wnorm d (z - z₀) + wnorm d (z' - z) := by
  obtain ⟨hz, w, hw⟩ := hm
  have hh : M *ᵥ (z' - z) = 0 := by rw [← slip_sub, slip_eq_of_normal hz' hz, sub_self]
  have hsplit : z' - z₀ = (z' - z) + (z - z₀) := by abel
  rw [hsplit, wnorm_add, hw, wpair_gauge_moving hd hh]
  ring

/-- [proved-standard; formal-checked] **The meeting point is the `D⁻¹`-nearest fixed point to the opening, alone.** -/
theorem meeting_nearest (hd : ∀ i, 0 < d i) {z₀ z z' : ι → ℝ} (hm : IsMeeting M c d z₀ z)
    (hz' : Normal M c z') :
    wnorm d (z - z₀) ≤ wnorm d (z' - z₀) ∧ (wnorm d (z' - z₀) = wnorm d (z - z₀) ↔ z' = z) := by
  rw [meeting_pythagoras (fun i => (hd i).ne') hm hz']
  refine ⟨le_add_of_nonneg_right (wnorm_nonneg (fun i => (hd i).le) _), ?_⟩
  rw [add_eq_left, wnorm_eq_zero_iff hd, sub_eq_zero]

/-- [proved-standard; formal-checked] At positive rates an opening has at most one meeting point. -/
theorem meeting_unique (hd : ∀ i, 0 < d i) {z₀ z₁ z₂ : ι → ℝ} (h₁ : IsMeeting M c d z₀ z₁)
    (h₂ : IsMeeting M c d z₀ z₂) : z₁ = z₂ := by
  have a := (meeting_nearest hd h₁ h₂.1).1
  have b := (meeting_nearest hd h₂ h₁.1).1
  exact ((meeting_nearest hd h₁ h₂.1).2.mp (le_antisymm b a)).symm

/-- [definition] The moving map `w ↦ D Mᵀw` as a linear map. -/
def moveLin (M : Matrix κ ι ℝ) (d : ι → ℝ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun w := d * (Mᵀ *ᵥ w)
  map_add' u v := by rw [mulVec_add, mul_add]
  map_smul' a u := by
    funext i
    simp only [mulVec_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype ι] in
/-- [definition] The moving map applied. -/
theorem moveLin_apply (w : κ → ℝ) : moveLin M d w = d * (Mᵀ *ᵥ w) := rfl

/-- [proved-standard; formal-checked] At positive rates `ker(Mᵀ G) = ker Mᵀ`. -/
theorem ker_normal_gram (hd : ∀ i, 0 < d i) :
    LinearMap.ker (Mᵀ.mulVecLin ∘ₗ M.mulVecLin ∘ₗ moveLin M d) = LinearMap.ker Mᵀ.mulVecLin := by
  ext w
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
    moveLin_apply]
  constructor
  · intro h
    have hg : gram M d w = 0 := by
      apply dotProduct_self_eq_zero.mp
      calc gram M d w ⬝ᵥ gram M d w = (d * (Mᵀ *ᵥ w)) ⬝ᵥ Mᵀ *ᵥ gram M d w := by
            rw [dotProduct_comm, gram, dot_mulVec, dotProduct_comm]
        _ = 0 := by unfold gram; rw [h, dotProduct_zero]
    have h0 : ∑ i, d i * (Mᵀ *ᵥ w) i ^ 2 = 0 := by rw [← dot_gram_eq_sum, hg, dotProduct_zero]
    exact (wsq_eq_zero_iff hd _).mp h0
  · intro h; rw [h, mul_zero, mulVec_zero, mulVec_zero]

/-- [proved-standard; formal-checked] **The meeting point exists** at positive rates, in finite dimension. -/
theorem exists_meeting (hd : ∀ i, 0 < d i) (z₀ : ι → ℝ) : ∃ z, IsMeeting M c d z₀ z := by
  set T := Mᵀ.mulVecLin ∘ₗ M.mulVecLin ∘ₗ moveLin M d
  have hfin : Module.finrank ℝ (LinearMap.range T) =
      Module.finrank ℝ (LinearMap.range Mᵀ.mulVecLin) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker T
    have h2 := LinearMap.finrank_range_add_finrank_ker Mᵀ.mulVecLin
    rw [ker_normal_gram hd] at h1
    omega
  have hrange : LinearMap.range T = LinearMap.range Mᵀ.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq (LinearMap.range_comp_le_range _ _) hfin
  have hmem : Mᵀ *ᵥ (-slip M c z₀) ∈ LinearMap.range T := by
    rw [hrange]; exact ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hmem
  refine ⟨z₀ + d * (Mᵀ *ᵥ w), ?_, w, by abel⟩
  have hs : slip M c (z₀ + d * (Mᵀ *ᵥ w)) = slip M c z₀ + gram M d w := by
    simp only [slip, gram, mulVec_add]; abel
  have hw' : Mᵀ *ᵥ gram M d w = Mᵀ *ᵥ (-slip M c z₀) := hw
  rw [Normal, hs, mulVec_add, hw', mulVec_neg, add_neg_cancel]

/-- [proved-standard; formal-checked] At equal rates the inverse-rate weight is the dot square over the rate. -/
theorem wnorm_const (r : ℝ) (u : ι → ℝ) : wnorm (fun _ => r) u = u ⬝ᵥ u / r := by
  simp only [wnorm, dotProduct, Finset.sum_div, sq]

/-- [proved-standard; formal-checked] **Equal rates:** the meeting point is the dot-nearest fixed point. -/
theorem equal_rates_nearest {r : ℝ} (hr : 0 < r) {z₀ z z' : ι → ℝ}
    (hm : IsMeeting M c (fun _ => r) z₀ z) (hz' : Normal M c z') :
    (z - z₀) ⬝ᵥ (z - z₀) ≤ (z' - z₀) ⬝ᵥ (z' - z₀) := by
  have h := (meeting_nearest (fun _ => hr) hm hz').1
  rwa [wnorm_const, wnorm_const, div_le_div_iff_of_pos_right hr] at h

/-! ## 5. Convergence -/

/-- [definition] **The spectral gap** `μ⟨w, Gw⟩ ≤ |Gw|²`, `0 < μ ≤ 1` (spectrally, `G² ⪰ μG`). -/
def Gap (M : Matrix κ ι ℝ) (d : ι → ℝ) (μ : ℝ) : Prop :=
  0 < μ ∧ μ ≤ 1 ∧ ∀ w, μ * (w ⬝ᵥ gram M d w) ≤ gram M d w ⬝ᵥ gram M d w

/-- [proved-standard; formal-checked] **One step contracts the `D⁻¹` distance to a normal point by `1 − μ`.** -/
theorem contraction (hd : ∀ i, d i ≠ 0) (hb : StepBound M d) {μ : ℝ} (hμ : Gap M d μ)
    {z' z : ι → ℝ} (hz' : Normal M c z') {ω : κ → ℝ} (hω : z - z' = d * (Mᵀ *ᵥ ω)) :
    step M c d z - z' = d * (Mᵀ *ᵥ (ω - M *ᵥ (z - z'))) ∧
      wnorm d (step M c d z - z') ≤ (1 - μ) * wnorm d (z - z') := by
  set u := z - z' with hu
  set x := M *ᵥ u with hx
  have hslip : Mᵀ *ᵥ slip M c z = Mᵀ *ᵥ x := by
    have : slip M c z = slip M c z' + x := by rw [hx, ← slip_sub]; abel
    rw [this, mulVec_add, hz', zero_add]
  have hnext : step M c d z - z' = u - d * (Mᵀ *ᵥ x) := by
    rw [step, hslip, hu]; abel
  refine ⟨by rw [hnext, hω, mulVec_sub, mul_sub], ?_⟩
  rw [hnext, wnorm_sub, wpair_weighted hd, wnorm_weighted, dot_transpose_mulVec, ← hx]
  have hgx := dot_gram_le hb x
  have hxg : x = gram M d ω := by rw [hx, hω, gram]
  have hun : wnorm d u = ω ⬝ᵥ gram M d ω := by rw [hω, wnorm_weighted]
  have hgap := hμ.2.2 ω
  rw [← hun, ← hxg] at hgap
  nlinarith

/-- [proved-standard; formal-checked] The iterates stay on the moving set of the meeting point and contract to it. -/
theorem iterate_contracts (hd : ∀ i, 0 < d i) (hb : StepBound M d) {μ : ℝ}
    (hμ : Gap M d μ) {z₀ z : ι → ℝ} (hm : IsMeeting M c d z₀ z) (t : ℕ) :
    (∃ ω, (step M c d)^[t] z₀ - z = d * (Mᵀ *ᵥ ω)) ∧
      wnorm d ((step M c d)^[t] z₀ - z) ≤ (1 - μ) ^ t * wnorm d (z₀ - z) := by
  have hd' : ∀ i, d i ≠ 0 := fun i => (hd i).ne'
  obtain ⟨hz, w, hw⟩ := hm
  induction t with
  | zero =>
      refine ⟨⟨-w, ?_⟩, by simp⟩
      rw [Function.iterate_zero_apply, mulVec_neg, mul_neg, ← hw]; abel
  | succ t ih =>
      obtain ⟨⟨ω, hω⟩, hle⟩ := ih
      obtain ⟨hmove, hcon⟩ := contraction hd' hb hμ hz hω
      rw [Function.iterate_succ_apply']
      refine ⟨⟨_, hmove⟩, ?_⟩
      have h1 : 0 ≤ 1 - μ := by linarith [hμ.2.1]
      calc wnorm d (step M c d ((step M c d)^[t] z₀) - z)
          ≤ (1 - μ) * wnorm d ((step M c d)^[t] z₀ - z) := hcon
        _ ≤ (1 - μ) * ((1 - μ) ^ t * wnorm d (z₀ - z)) := mul_le_mul_of_nonneg_left hle h1
        _ = (1 - μ) ^ (t + 1) * wnorm d (z₀ - z) := by ring

/-- [proved-standard; formal-checked] **Geometric convergence:** `|z_t − z*|²_(D⁻¹) ≤ (1 − μ)^t |z₀ − z*|²_(D⁻¹)`. -/
theorem converges_geometric (hd : ∀ i, 0 < d i) (hb : StepBound M d) {μ : ℝ}
    (hμ : Gap M d μ) {z₀ z : ι → ℝ} (hm : IsMeeting M c d z₀ z) (t : ℕ) :
    wnorm d ((step M c d)^[t] z₀ - z) ≤ (1 - μ) ^ t * wnorm d (z₀ - z) :=
  (iterate_contracts hd hb hμ hm t).2

/-- [proved-standard; formal-checked] **The slip converges geometrically to the cokernel residual.** -/
theorem slip_converges (hd : ∀ i, 0 < d i) (hb : StepBound M d) {μ : ℝ}
    (hμ : Gap M d μ) {z₀ z : ι → ℝ} (hm : IsMeeting M c d z₀ z) (t : ℕ) :
    (slip M c ((step M c d)^[t] z₀) - slip M c z) ⬝ᵥ (slip M c ((step M c d)^[t] z₀) - slip M c z)
      ≤ (1 - μ) ^ t * wnorm d (z₀ - z) := by
  obtain ⟨⟨ω, hω⟩, hle⟩ := iterate_contracts hd hb hμ hm t
  rw [slip_sub, hω]
  have h := gram_sq_le hb ω
  rw [← wnorm_weighted, ← hω] at h
  exact h.trans hle

/-- [proved-standard; formal-checked] **The iterates converge to the meeting point** under the step bound and a gap. -/
theorem tendsto_meeting (hd : ∀ i, 0 < d i) (hb : StepBound M d) {μ : ℝ}
    (hμ : Gap M d μ) {z₀ z : ι → ℝ} (hm : IsMeeting M c d z₀ z) :
    Filter.Tendsto (fun t => (step M c d)^[t] z₀) Filter.atTop (nhds z) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ t : ℕ, ‖(step M c d)^[t] z₀ i - z i‖ ≤
      √(d i * ((1 - μ) ^ t * wnorm d (z₀ - z))) := by
    intro t
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    have h1 : ((step M c d)^[t] z₀ - z) i ^ 2 / d i ≤ wnorm d ((step M c d)^[t] z₀ - z) :=
      Finset.single_le_sum (f := fun j => ((step M c d)^[t] z₀ - z) j ^ 2 / d j)
        (fun j _ => div_nonneg (sq_nonneg _) (hd j).le) (Finset.mem_univ i)
    have h2 := converges_geometric hd hb hμ hm t
    rw [div_le_iff₀ (hd i)] at h1
    simp only [Pi.sub_apply] at h1
    nlinarith [hd i]
  have h0 : 0 ≤ 1 - μ := by linarith [hμ.2.1]
  have h1 : 1 - μ < 1 := by linarith [hμ.1]
  have hlim : Filter.Tendsto (fun t : ℕ => √(d i * ((1 - μ) ^ t * wnorm d (z₀ - z))))
      Filter.atTop (nhds 0) := by
    have := (((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const
      (wnorm d (z₀ - z))).const_mul (d i)).sqrt
    simpa using this
  exact squeeze_zero (fun t => norm_nonneg _) hbound hlim

/-- [proved-standard; formal-checked] **The gap holds at positive rates in finite dimension** (by compactness). -/
theorem exists_gap (hd : ∀ i, 0 < d i) : ∃ μ, Gap M d μ := by
  set V := LinearMap.range (moveLin M d)
  set S : Set (ι → ℝ) := (V : Set (ι → ℝ)) ∩ wnorm d ⁻¹' {1} with hSdef
  set f : (ι → ℝ) → ℝ := fun u => M *ᵥ u ⬝ᵥ M *ᵥ u with hfdef
  have hwc : Continuous (wnorm d) :=
    continuous_finsetSum _ fun i _ => ((continuous_apply i).pow 2).div_const _
  have hfc : Continuous f := by
    have hM : Continuous fun u : ι → ℝ => M *ᵥ u := M.mulVecLin.continuous_of_finiteDimensional
    exact continuous_finsetSum _ fun k _ =>
      ((continuous_apply k).comp hM).mul ((continuous_apply k).comp hM)
  have hScompact : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (Submodule.closed_of_finiteDimensional V).inter (isClosed_singleton.preimage hwc)
    · rw [isBounded_iff_forall_norm_le]
      have hsum : 0 ≤ ∑ j, d j := Finset.sum_nonneg fun j _ => (hd j).le
      refine ⟨1 + ∑ j, d j, fun u hu => ?_⟩
      refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
      rw [Real.norm_eq_abs]
      have hu1 : wnorm d u = 1 := hu.2
      have h1 : u i ^ 2 / d i ≤ wnorm d u :=
        Finset.single_le_sum (f := fun j => u j ^ 2 / d j)
          (fun j _ => div_nonneg (sq_nonneg _) (hd j).le) (Finset.mem_univ i)
      rw [hu1, div_le_iff₀ (hd i), one_mul] at h1
      have h2 : d i ≤ ∑ j, d j := Finset.single_le_sum (fun j _ => (hd j).le) (Finset.mem_univ i)
      nlinarith [sq_abs (u i), abs_nonneg (u i), sq_nonneg (|u i| - 1)]
  have hfmove : ∀ w, f (moveLin M d w) = gram M d w ⬝ᵥ gram M d w := fun w => rfl
  have hpos : ∀ u ∈ S, 0 < f u := by
    rintro u ⟨⟨w, rfl⟩, hu1⟩
    have hu1' : wnorm d (moveLin M d w) = 1 := hu1
    rw [moveLin_apply, wnorm_weighted] at hu1'
    rw [hfmove]
    rcases (dot_self_nonneg (gram M d w)).eq_or_lt with h0 | h0
    · have hg : gram M d w = 0 := dotProduct_self_eq_zero.mp h0.symm
      rw [hg, dotProduct_zero] at hu1'
      norm_num at hu1'
    · exact h0
  have hscale : ∀ w : κ → ℝ, 0 < w ⬝ᵥ gram M d w →
      (1 / √(w ⬝ᵥ gram M d w)) • moveLin M d w ∈ S ∧
        f ((1 / √(w ⬝ᵥ gram M d w)) • moveLin M d w) =
          gram M d w ⬝ᵥ gram M d w / (w ⬝ᵥ gram M d w) := by
    intro w hs
    have ha : (1 / √(w ⬝ᵥ gram M d w)) ^ 2 = 1 / (w ⬝ᵥ gram M d w) := by
      rw [div_pow, one_pow, Real.sq_sqrt hs.le]
    refine ⟨⟨V.smul_mem _ ⟨w, rfl⟩, ?_⟩, ?_⟩
    · show wnorm d _ = 1
      rw [wnorm_smul, ha, moveLin_apply, wnorm_weighted, one_div, inv_mul_cancel₀ hs.ne']
    · have hg : M *ᵥ moveLin M d w ⬝ᵥ M *ᵥ moveLin M d w = gram M d w ⬝ᵥ gram M d w := rfl
      simp only [hfdef, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      rw [hg, ← mul_assoc, ← sq, ha]
      ring
  by_cases hS : S.Nonempty
  · obtain ⟨u₀, hu₀, hmin⟩ := hScompact.exists_isMinOn hS hfc.continuousOn
    refine ⟨min (f u₀) 1, lt_min (hpos u₀ hu₀) one_pos, min_le_right _ _, fun w => ?_⟩
    rcases (dot_gram_nonneg (fun i => (hd i).le) M w).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact dot_self_nonneg _
    · obtain ⟨hmem, hval⟩ := hscale w h0
      have h1 := isMinOn_iff.mp hmin _ hmem
      rw [hval, le_div_iff₀ h0] at h1
      calc min (f u₀) 1 * (w ⬝ᵥ gram M d w) ≤ f u₀ * (w ⬝ᵥ gram M d w) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) h0.le
        _ ≤ _ := h1
  · refine ⟨1, one_pos, le_rfl, fun w => ?_⟩
    rcases (dot_gram_nonneg (fun i => (hd i).le) M w).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact dot_self_nonneg _
    · exact absurd ⟨_, (hscale w h0).1⟩ hS

/-- [proved-standard; formal-checked] **The iterates converge to the meeting point** under the step bound alone. -/
theorem tendsto_meeting' (hd : ∀ i, 0 < d i) (hb : StepBound M d) {z₀ z : ι → ℝ}
    (hm : IsMeeting M c d z₀ z) :
    Filter.Tendsto (fun t => (step M c d)^[t] z₀) Filter.atTop (nhds z) := by
  obtain ⟨μ, hμ⟩ := exists_gap (M := M) hd
  exact tendsto_meeting hd hb hμ hm

/-- [proved-standard; formal-checked] **Any limit of the iterates is the meeting point.** -/
theorem limit_eq_meeting (hd : ∀ i, 0 < d i) (hb : StepBound M d) {z₀ z zLim : ι → ℝ}
    (hm : IsMeeting M c d z₀ z)
    (hlim : Filter.Tendsto (fun t => (step M c d)^[t] z₀) Filter.atTop (nhds zLim)) : zLim = z :=
  tendsto_nhds_unique hlim (tendsto_meeting' hd hb hm)

/-! ## 6. Key location: continuous keys -/

/-- [definition] **The keys of a menu of linear contacts**: the fibre `{z | Mz = c}` of the closure map. -/
def keys (M : Matrix κ ι ℝ) (c : κ → ℝ) : Set (ι → ℝ) := {z | M *ᵥ z = c}

omit [Fintype κ] in
/-- [proved-derived; formal-checked] **The keys are `ker M`-gauge invariant** (cf. `Keys.fibre_gauge_invariant`). -/
theorem keys_gauge_invariant {h : ι → ℝ} (hh : M *ᵥ h = 0) (z : ι → ℝ) :
    z + h ∈ keys M c ↔ z ∈ keys M c := by
  simp only [keys, Set.mem_ofPred_eq, mulVec_add, hh, add_zero]

omit [Fintype κ] in
/-- [proved-derived; formal-checked] **A nonempty fibre of keys is one gauge orbit** (cf. `Keys.fibre_eq_orbit`). -/
theorem keys_eq_orbit {z₁ : ι → ℝ} (h₁ : z₁ ∈ keys M c) :
    keys M c = {z | ∃ h, M *ᵥ h = 0 ∧ z = z₁ + h} := by
  ext z
  constructor
  · intro hz
    refine ⟨z - z₁, ?_, by abel⟩
    have hz' : M *ᵥ z = c := hz
    have h₁' : M *ᵥ z₁ = c := h₁
    rw [mulVec_sub, hz', h₁', sub_self]
  · rintro ⟨h, hh, rfl⟩
    exact (keys_gauge_invariant hh z₁).mpr h₁

/-- [proved-derived; formal-checked] **With a matched pair, the keys are the fixed points of deposition.** -/
theorem mem_keys_iff_isFixed (hd : ∀ i, d i ≠ 0) (hne : (keys M c).Nonempty) (z : ι → ℝ) :
    z ∈ keys M c ↔ IsFixed M c d z := by
  obtain ⟨z₁, hz₁⟩ := hne
  rw [isFixed_iff_normal hd, normal_iff_matched ⟨z₁, hz₁⟩, slip, sub_eq_zero]
  rfl

/-- [proved-derived; formal-checked] **Gauge fixing by the opening:** one key has zero gauge component from `z₀`. -/
theorem gauge_fix_unique (hd : ∀ i, 0 < d i) (hne : (keys M c).Nonempty) (z₀ : ι → ℝ) :
    ∃! z, z ∈ keys M c ∧ ∀ h, M *ᵥ h = 0 → wpair d h (z - z₀) = 0 := by
  have hd' : ∀ i, d i ≠ 0 := fun i => (hd i).ne'
  obtain ⟨z, hz, w, hw⟩ := exists_meeting (c := c) hd z₀
  have hzk : z ∈ keys M c :=
    (mem_keys_iff_isFixed hd' hne z).mpr ((isFixed_iff_normal hd' z).mpr hz)
  refine ⟨z, ⟨hzk, fun h hh => by rw [hw, wpair_gauge_moving hd' hh]⟩, ?_⟩
  rintro z' ⟨hz', hg⟩
  have hzk' : M *ᵥ z = c := hzk
  have hz'' : M *ᵥ z' = c := hz'
  have hh : M *ᵥ (z' - z) = 0 := by rw [mulVec_sub, hz'', hzk', sub_self]
  have e2 : wpair d (z' - z) (z - z₀) = 0 := by rw [hw, wpair_gauge_moving hd' hh]
  have hsplit : z' - z = (z' - z₀) - (z - z₀) := by abel
  have h0 : wnorm d (z' - z) = 0 := by
    rw [← wpair_self]
    conv_lhs => arg 3; rw [hsplit]
    rw [wpair_sub_right, hg _ hh, e2, sub_zero]
  exact sub_eq_zero.mp ((wnorm_eq_zero_iff hd _).mp h0)

/-- [proved-derived; formal-checked] **Two-sided deposition locates the gauge-fixed key**, the `D⁻¹`-nearest to `z₀`. -/
theorem deposition_locates_key (hd : ∀ i, 0 < d i) (hb : StepBound M d)
    (hne : (keys M c).Nonempty) (z₀ : ι → ℝ) :
    ∃ z, z ∈ keys M c ∧ (∀ h, M *ᵥ h = 0 → wpair d h (z - z₀) = 0) ∧
      (∀ z' ∈ keys M c, wnorm d (z - z₀) ≤ wnorm d (z' - z₀)) ∧
      Filter.Tendsto (fun t => (step M c d)^[t] z₀) Filter.atTop (nhds z) := by
  have hd' : ∀ i, d i ≠ 0 := fun i => (hd i).ne'
  obtain ⟨z, hm⟩ := exists_meeting (c := c) hd z₀
  obtain ⟨hz, w, hw⟩ := hm
  refine ⟨z, (mem_keys_iff_isFixed hd' hne z).mpr ((isFixed_iff_normal hd' z).mpr hz),
    fun h hh => by rw [hw, wpair_gauge_moving hd' hh], fun z' hz' => ?_,
    tendsto_meeting' hd hb ⟨hz, w, hw⟩⟩
  exact (meeting_nearest hd ⟨hz, w, hw⟩
    ((isFixed_iff_normal hd' z').mp ((mem_keys_iff_isFixed hd' hne z').mp hz'))).1

/-! ## 7. The two-sided reading: key `x`, lock `y` -/

section TwoSided

variable {X Y K : Type*} [Fintype X] [Fintype Y] [Fintype K]

/-- [definition] **The contact's slip** `Δ = Ax − By − c` between the key `x` and the lock `y`. -/
def twoSlip (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (x : X → ℝ) (y : Y → ℝ) :
    K → ℝ :=
  A *ᵥ x - B *ᵥ y - c

/-- [definition] **Two-sided deposition:** `x ← x − αAᵀΔ`, `y ← y + βBᵀΔ`. -/
def twoStep (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α β : ℝ) (x : X → ℝ)
    (y : Y → ℝ) : (X → ℝ) × (Y → ℝ) :=
  (x - α • (Aᵀ *ᵥ twoSlip A B c x y), y + β • (Bᵀ *ᵥ twoSlip A B c x y))

/-- [definition] **The joint reading** `M = [A, −B]`, the contact's slip map. -/
def joint (A : Matrix K X ℝ) (B : Matrix K Y ℝ) : Matrix K (X ⊕ Y) ℝ := fromCols A (-B)

/-- [definition] **The rates** `D = diag(α, β)`, `α` on the key and `β` on the lock. -/
def rates (α β : ℝ) : X ⊕ Y → ℝ := Sum.elim (fun _ => α) (fun _ => β)

omit [Fintype K] in
/-- [proved-derived; formal-checked] The joint slip of `z = (x, y)` is the contact's slip. -/
theorem slip_joint (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (x : X → ℝ) (y : Y → ℝ) :
    slip (joint A B) c (Sum.elim x y) = twoSlip A B c x y := by
  rw [slip, joint, fromCols_mulVec_sumElim, neg_mulVec, twoSlip, sub_eq_add_neg (A *ᵥ x)]

omit [Fintype X] [Fintype Y] in
/-- [proved-derived; formal-checked] `MᵀΔ = (AᵀΔ, −BᵀΔ)`: the covectors reaching the key and the lock. -/
theorem joint_transpose_mulVec (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (w : K → ℝ) :
    (joint A B)ᵀ *ᵥ w = Sum.elim (Aᵀ *ᵥ w) (-(Bᵀ *ᵥ w)) := by
  rw [joint, transpose_fromCols, fromRows_mulVec, transpose_neg, neg_mulVec]

/-- [proved-derived; formal-checked] **The joint step is the pair of side updates.** -/
theorem step_joint (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α β : ℝ) (x : X → ℝ)
    (y : Y → ℝ) :
    step (joint A B) c (rates α β) (Sum.elim x y) =
      Sum.elim (twoStep A B c α β x y).1 (twoStep A B c α β x y).2 := by
  funext i
  rcases i with i | i <;>
    simp [step, slip_joint, joint_transpose_mulVec, rates, twoStep, sub_eq_add_neg]

/-- [proved-derived; formal-checked] **One step lowers the slip by both deposits:** `Δ⁺ = Δ − αAAᵀΔ − βBBᵀΔ`. -/
theorem twoSlip_step (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α β : ℝ) (x : X → ℝ)
    (y : Y → ℝ) :
    twoSlip A B c (twoStep A B c α β x y).1 (twoStep A B c α β x y).2 =
      twoSlip A B c x y - α • (A *ᵥ (Aᵀ *ᵥ twoSlip A B c x y)) -
        β • (B *ᵥ (Bᵀ *ᵥ twoSlip A B c x y)) := by
  simp only [twoStep, twoSlip, mulVec_sub, mulVec_add, mulVec_smul]
  abel

/-- [proved-derived; formal-checked] **A pair is fixed iff both sides' covectors `AᵀΔ` and `BᵀΔ` vanish.** -/
theorem twoStep_fixed_iff (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) {α β : ℝ} (hα : α ≠ 0)
    (hβ : β ≠ 0) (x : X → ℝ) (y : Y → ℝ) :
    twoStep A B c α β x y = (x, y) ↔
      Aᵀ *ᵥ twoSlip A B c x y = 0 ∧ Bᵀ *ᵥ twoSlip A B c x y = 0 := by
  simp only [twoStep, Prod.mk.injEq, sub_eq_self, add_eq_left, smul_eq_zero, hα, hβ, false_or]

omit [Fintype X] [Fintype Y] in
/-- [proved-derived; formal-checked] **The moving directions are the sides' shares** `(αAᵀw, −βBᵀw)` of one covector. -/
theorem rates_moving_joint (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (α β : ℝ) (w : K → ℝ) :
    rates α β * ((joint A B)ᵀ *ᵥ w) = Sum.elim (α • (Aᵀ *ᵥ w)) (-(β • (Bᵀ *ᵥ w))) := by
  rw [joint_transpose_mulVec]
  funext i
  rcases i with i | i <;> simp [rates]

/-- [proved-standard; formal-checked] The scalar inequality behind the two-sided step bound. -/
theorem scalar_bound {α β a b P Q R p q : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (ha : 0 < a) (hb : 0 < b)
    (hP : P ≤ a * p) (hQ : Q ≤ b * q) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (haux : 0 ≤ b ^ 2 * P + 2 * a * b * R + a ^ 2 * Q) (hab : α * a + β * b ≤ 1) :
    α ^ 2 * P - 2 * α * β * R + β ^ 2 * Q ≤ α * p + β * q := by
  have h1 : a * b * (α ^ 2 * P - 2 * α * β * R + β ^ 2 * Q) ≤
      (α * a + β * b) * (α * b * P + β * a * Q) := by
    nlinarith [mul_nonneg (mul_nonneg hα hβ) haux]
  have h2 : α * b * P + β * a * Q ≤ a * b * (α * p + β * q) := by
    nlinarith [mul_le_mul_of_nonneg_left hP (mul_nonneg hα hb.le),
      mul_le_mul_of_nonneg_left hQ (mul_nonneg hβ ha.le)]
  have h3 : 0 ≤ α * a + β * b := by positivity
  have h4 : 0 ≤ a * b * (α * p + β * q) := by positivity
  have h5 : (α * a + β * b) * (α * b * P + β * a * Q) ≤ a * b * (α * p + β * q) :=
    calc (α * a + β * b) * (α * b * P + β * a * Q)
        ≤ (α * a + β * b) * (a * b * (α * p + β * q)) := mul_le_mul_of_nonneg_left h2 h3
      _ ≤ 1 * (a * b * (α * p + β * q)) := mul_le_mul_of_nonneg_right hab h4
      _ = a * b * (α * p + β * q) := one_mul _
  exact le_of_mul_le_mul_left (h1.trans h5) (mul_pos ha hb)

/-- [proved-derived; formal-checked] **`α‖A‖² + β‖B‖² ≤ 1` gives the step bound** of the joint reading. -/
theorem stepBound_joint {A : Matrix K X ℝ} {B : Matrix K Y ℝ} {α β a b : ℝ} (hα : 0 ≤ α)
    (hβ : 0 ≤ β) (ha : 0 < a) (hb : 0 < b) (hA : ∀ v, A *ᵥ v ⬝ᵥ A *ᵥ v ≤ a * (v ⬝ᵥ v))
    (hB : ∀ v, B *ᵥ v ⬝ᵥ B *ᵥ v ≤ b * (v ⬝ᵥ v)) (hab : α * a + β * b ≤ 1) :
    StepBound (joint A B) (rates α β) := by
  intro v
  obtain ⟨p, q, rfl⟩ : ∃ p q, v = Sum.elim p q :=
    ⟨v ∘ Sum.inl, v ∘ Sum.inr, (Sum.elim_comp_inl_inr v).symm⟩
  have hv : rates α β * Sum.elim p q = Sum.elim (α • p) (β • q) := by
    funext i; rcases i with i | i <;> simp [rates]
  rw [hv, joint, fromCols_mulVec_sumElim, sumElim_dotProduct_sumElim, neg_mulVec, mulVec_smul,
    mulVec_smul]
  have hc : B *ᵥ q ⬝ᵥ A *ᵥ p = A *ᵥ p ⬝ᵥ B *ᵥ q := dotProduct_comm _ _
  have haux : 0 ≤ (b • A *ᵥ p + a • B *ᵥ q) ⬝ᵥ (b • A *ᵥ p + a • B *ᵥ q) := dot_self_nonneg _
  simp only [add_dotProduct, dotProduct_add, neg_dotProduct, dotProduct_neg, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hc] at haux ⊢
  have := scalar_bound hα hβ ha hb (hA p) (hB q) (dot_self_nonneg p) (dot_self_nonneg q)
    (R := A *ᵥ p ⬝ᵥ B *ᵥ q) (by nlinarith [haux]) hab
  nlinarith [this]

/-- [proved-derived; formal-checked] **Conservation at every rate:** `β⟨h_x, x⟩ + α⟨h_y, y⟩`, `A h_x = B h_y`. -/
theorem twoStep_conserves (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α β : ℝ)
    (x : X → ℝ) (y : Y → ℝ) {hx : X → ℝ} {hy : Y → ℝ} (hh : A *ᵥ hx = B *ᵥ hy) :
    β * (hx ⬝ᵥ (twoStep A B c α β x y).1) + α * (hy ⬝ᵥ (twoStep A B c α β x y).2) =
      β * (hx ⬝ᵥ x) + α * (hy ⬝ᵥ y) := by
  simp only [twoStep, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dot_transpose_mulVec, hh]
  ring

/-- [proved-derived; formal-checked] **One-sided deposition:** at `β = 0` the lock stays; the key steps alone. -/
theorem twoStep_rate_zero (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α : ℝ)
    (x : X → ℝ) (y : Y → ℝ) :
    (twoStep A B c α 0 x y).2 = y ∧
      (twoStep A B c α 0 x y).1 = step A (c + B *ᵥ y) (fun _ => α) x := by
  have hs : slip A (c + B *ᵥ y) x = twoSlip A B c x y := by simp only [slip, twoSlip]; abel
  refine ⟨by simp [twoStep], ?_⟩
  funext i
  simp [twoStep, step, hs]

/-- [proved-derived; formal-checked] **Neither side comes first:** exchanging lock and key exchanges the updates. -/
theorem twoStep_swap (A : Matrix K X ℝ) (B : Matrix K Y ℝ) (c : K → ℝ) (α β : ℝ)
    (x : X → ℝ) (y : Y → ℝ) :
    twoStep B A (-c) β α y x = ((twoStep A B c α β x y).2, (twoStep A B c α β x y).1) := by
  have hs : twoSlip B A (-c) y x = -twoSlip A B c x y := by simp only [twoSlip]; abel
  refine Prod.ext ?_ ?_
  · simp only [twoStep, hs, mulVec_neg, smul_neg, sub_neg_eq_add]
  · simp only [twoStep, hs, mulVec_neg, smul_neg]
    abel

end TwoSided

/-! ## 8. The scalar witness -/

section Witness

/-- [definition] The scalar contact's readings `A = B = 1`. -/
abbrev one₁ : Matrix (Fin 1) (Fin 1) ℝ := 1

/-- [proved-derived; formal-checked] **Equal rates `½`:** from `(1, 0)` one step reaches `(½, ½)`, matched. -/
theorem witness_equal_rates :
    twoStep one₁ one₁ 0 (1 / 2) (1 / 2) (fun _ => 1) (fun _ => 0) =
        ((fun _ => 1 / 2), (fun _ => 1 / 2)) ∧
      twoSlip one₁ one₁ 0 (fun _ => 1 / 2) (fun _ => 1 / 2) = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [twoStep, twoSlip, one₁, one_mulVec, transpose_one, Prod.mk.injEq]
    constructor <;> funext i <;> norm_num
  · funext i; simp [twoSlip]

/-- [proved-derived; formal-checked] The witness's rates hold the step bound (`a = b = 1`, `½ + ½ ≤ 1`). -/
theorem witness_stepBound : StepBound (joint one₁ one₁) (rates (1 / 2) (1 / 2)) :=
  stepBound_joint (a := 1) (b := 1) (by norm_num) (by norm_num) one_pos one_pos
    (fun v => by simp [one₁]) (fun v => by simp [one₁]) (by norm_num)

/-- [proved-derived; formal-checked] **The midpoint `(½, ½)` is the meeting point from `(1, 0)`.** -/
theorem witness_meeting :
    IsMeeting (joint one₁ one₁) 0 (rates (1 / 2) (1 / 2)) (Sum.elim (fun _ => 1) (fun _ => 0))
      (Sum.elim (fun _ => 1 / 2) (fun _ => 1 / 2)) := by
  refine ⟨?_, fun _ => -1, ?_⟩
  · rw [Normal, slip_joint, witness_equal_rates.2, mulVec_zero]
  · rw [rates_moving_joint]
    funext i
    rcases i with i | i <;> norm_num [one₁]

/-- [proved-derived; formal-checked] **The key alone moves:** `α = 1, β = 0` gives `(0, 0)`; `α = ½` gives `(½, 0)`. -/
theorem witness_key_alone :
    twoStep one₁ one₁ 0 1 0 (fun _ => 1) (fun _ => 0) = ((fun _ => 0), (fun _ => 0)) ∧
      twoStep one₁ one₁ 0 (1 / 2) 0 (fun _ => 1) (fun _ => 0) = ((fun _ => 1 / 2), (fun _ => 0)) ∧
      twoSlip one₁ one₁ 0 (fun _ => 1 / 2) (fun _ => 0) = fun _ => 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [twoStep, twoSlip, one₁, one_mulVec, transpose_one, Prod.mk.injEq]
    constructor <;> funext i <;> norm_num
  · simp only [twoStep, twoSlip, one₁, one_mulVec, transpose_one, Prod.mk.injEq]
    constructor <;> funext i <;> norm_num
  · funext i; simp [twoSlip]

/-- [proved-derived; formal-checked] **A residual no deposition removes:** `A = (1, 1)ᵀ`, `B = 0`, `c = (0, 2)`. -/
theorem witness_residual (α β : ℝ) :
    twoStep !![(1 : ℝ); 1] (0 : Matrix (Fin 2) (Fin 1) ℝ) ![0, 2] α β (fun _ => 1) (fun _ => 0) =
        ((fun _ => 1), (fun _ => 0)) ∧
      twoSlip !![(1 : ℝ); 1] (0 : Matrix (Fin 2) (Fin 1) ℝ) ![0, 2] (fun _ => 1) (fun _ => 0) =
        ![1, -1] := by
  have hs : twoSlip !![(1 : ℝ); 1] (0 : Matrix (Fin 2) (Fin 1) ℝ) ![0, 2] (fun _ => 1)
      (fun _ => 0) = ![1, -1] := by
    funext i; fin_cases i <;> norm_num [twoSlip, dotProduct]
  refine ⟨?_, hs⟩
  rw [twoStep, hs]
  simp only [Prod.mk.injEq]
  constructor <;> funext i <;> fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two]

end Witness

end Holonics.HNN.ContactFixedPoint
