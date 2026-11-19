import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Block
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-!
# The Half pump holds the harmonic mode on a shear, and its signed form certifies exactly up to `p = d/h`

The founded ring of October 18 (#398, merged as `16b488dc`; the comment owing this on #62 is c6249536068, item 5; atlas
`hnn.half-pump-harmonic-monodromy`) is a ring's resonator, `Constitution::with_founded_dynamics`, with dissipation
`d = 1/Y` and a Half pump of strength `p` on its phase-zero axis. Its tick (the October ring's header,
`crates/holonics/src/hnn/ring.rs@d5ed4adc1`):

```text
pump     K_t = K + ⊕_k −2p [[cos ψ_t, sin ψ_t], [sin ψ_t, −cos ψ_t]],   e^(iψ_t) = a² s^t
solve    M_t ω = 2C w − h K_t u,   M_t = 2C + (h/Y) I + h D + (h²/2) K_t
state    u′ = u + h ω,   w′ = 2ω − w
```

with `s = −1` for the Half pump, so the period is two ticks and the node block at the second tick is the first's negative.
Its certificate (`ResonatorMaterial::certify`) asks, at every pump phase, that the signed form `2C + hD + (h²/2) K_t` be
positive semidefinite. The Rust test `half_pump_at_critical_coupling_has_the_stipulated_harmonic_monodromy` checks both
statements on periods 2, 3 and 5; this file proves them.

[proved-derived; formal-checked] What is proved.

1. **The tick on a harmonic vector** (`operator_harmonic`, `tick_harmonic`): where `C v = 0`, `D v = d v` and the
   phase's stiffness reads `K_t v = κ v`, the operator reads `M_t v = (h/Y + hd + (h²/2)κ) v`, and the tick of any
   executed solve `X` with `X M_t = 1` keeps the pair `(αv, βv)` on the line of `v`, with the coefficients stated.
2. **The period map is a shear** (`half_pump_harmonic_monodromy`): with `a = h/Y + hd`, `b = h²p`, the stiffness
   blind to the harmonic vector (`K v = 0`) and the pump reading `P v = −2p v` there (its in-phase sheet), the two ticks
   `K₀ = K + P`, `K₁ = K − P` send `(αv, βv)` to `(αv, (β − 8hpα/(a − b)) v)`: on the harmonic in-phase pair `(u, w)`
   the monodromy `T₁T₀` is `[[1, 0], [−8hp/(a − b), 1]]` for every `p` with `a ≠ b` and `a + b ≠ 0` (`shear`,
   `half_pump_harmonic_monodromy_matrix`). Its determinant is one and its trace two (`shear_det`, `shear_trace`): both
   multipliers are one, and the harmonic mode is held on a parabolic move, free fall between the pump's two grips.
3. **The signed form certifies exactly up to the edge** (`signedForm_quadratic`, `half_pump_edge_certifies`,
   `half_pump_edge_singular`): with `C, K ⪰ 0`, `D = d I`, a pump bounded by its strength (`|⟨z, P z⟩| ≤ 2p|z|²`, a
   reflection scaled by `2p`) and a harmonic vector `v ≠ 0` on which `P` reads `−2p`, both phases' signed forms are
   positive semidefinite iff `p ≤ d/h`; at `p = d/h` the first phase's form sends `v` to zero, so the form is
   positive semidefinite and singular there.
4. **A certified phase solves uniquely** (`operator_quadratic`, `operator_det_ne_zero`): where the signed form is
   positive semidefinite and `h/Y > 0`, `⟨z, M_t z⟩ ≥ (h/Y)|z|²`, so `M_t` is invertible and its inverse is an executed
   solve of statement 2 (`half_pump_certified_monodromy`, with `a − b ≥ h/Y > 0` read from `p ≤ d/h`).
5. **The ring the Rust declares** (`cyclicIncidence_harmonic`, `weightedForm_harmonic`, `weightedForm_nonneg`,
   `realify_quadratic`, `phaseZeroPump_harmonic`, `phaseZeroPump_bound`, `cyclic_half_pump_edge_certifies`,
   `cyclic_half_pump_monodromy`): on the cyclic incidence `(Bx)_i = x_(i+1) − x_i` with nonnegative weights,
   `C = BᵀW_C B` and `K = BᵀW_K B` realified on the two coordinates of each node, `D = dI` and the Half pump's block on
   its phase-zero axis, every hypothesis above holds for the harmonic in-phase vector (real part one at every node,
   imaginary part zero), so the two statements hold on that ring for any nonnegative weights, unit weights among them.
6. **The declared cases** (`declared_entries`, `declared_edges`): `(Y, h, p) = (2, 1, 1/2), (2, 1, 1/4), (3, 2, 1/6),
   (3, 2, 1/12)` give the entries `−8, −8/3, −4, −4/3` the Rust test fixes, each at or under its edge `d/h`, and the
   refused cases `p = 65/128, 1` at `(2, 1)` and `65/384, 1/3` at `(3, 2)` stand past it.

Limits. The realified layout here is the two coordinates as two blocks (`Fin n ⊕ Fin n`) where the Rust interleaves
them; the forms agree under that permutation. The cyclic incidence here reads `(Bx)_i = x_(i+1) − x_i` on `Fin n`,
which is the Rust's for every period `n ≥ 2` (a period of one is the zero matrix here). Only the harmonic in-phase pair
is computed; the monodromy on the other modes, the pump on a general axis and the lattice chart's executed solve (the
statements take any left inverse, the exact law's) are not here.

The computational object is the helical pair interaction: the ring's two pumped reflections are the grips of the
parametron's swing, and the harmonic in-phase pair is the mode their contacts do not reach (`B·1 = 0`), which the two
grips move by a shear alone. Of the winding guide's six general objects this touches the helix (the ring's pump phases
over its period), the pair (the incidence's contacts) and faces and placement (the in-phase sheet `P v = −2pv`); the
cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `hnn.half-pump-harmonic-monodromy` (and `hnn.founded-field-extension`, which uses it); #410's
box on the Half pump, beside `Holonics/HNN/Ring` (`ring_harmonic_mode_singular`, `pumpBlock`) and `Holonics/HNN/Floquet`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.HalfPumpMonodromy

open Matrix

section Tick

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The phase's operator** `M = 2C + (h/Y) I + h D + (h²/2) K`. -/
noncomputable def operator (C D K : Matrix ι ι ℝ) (Y h : ℝ) : Matrix ι ι ℝ :=
  (2 : ℝ) • C + (h / Y) • (1 : Matrix ι ι ℝ) + h • D + (h ^ 2 / 2) • K

/-- [definition] **The tick** with the executed solve `X`: `ω = X(2Cw − hKu)`, `u′ = u + hω`, `w′ = 2ω − w`. -/
def tick (C K X : Matrix ι ι ℝ) (h : ℝ) (s : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (s.1 + h • (X *ᵥ ((2 : ℝ) • (C *ᵥ s.2) - h • (K *ᵥ s.1))),
    (2 : ℝ) • (X *ᵥ ((2 : ℝ) • (C *ᵥ s.2) - h • (K *ᵥ s.1))) - s.2)

/-- [proved-derived] **The operator on a harmonic vector**: `M v = (h/Y + hd + (h²/2)κ) v`. -/
theorem operator_harmonic {C D K : Matrix ι ι ℝ} {Y h d κ : ℝ} {v : ι → ℝ} (hC : C *ᵥ v = 0)
    (hD : D *ᵥ v = d • v) (hK : K *ᵥ v = κ • v) :
    operator C D K Y h *ᵥ v = (h / Y + h * d + h ^ 2 / 2 * κ) • v := by
  unfold operator
  simp only [add_mulVec, smul_mulVec, one_mulVec, hC, hD, hK]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  ring

/-- [proved-derived] **The tick keeps the harmonic line**: with `C v = 0`, `K v = κ v`, `M v = m v`, `m ≠ 0` and an
executed solve `X M = 1`, the tick sends `(αv, βv)` to `((α − h²κα/m) v, (−2hκα/m − β) v)`. -/
theorem tick_harmonic {C D K X : Matrix ι ι ℝ} {Y h κ m : ℝ} {v : ι → ℝ} (hC : C *ᵥ v = 0)
    (hK : K *ᵥ v = κ • v) (hM : operator C D K Y h *ᵥ v = m • v) (hX : X * operator C D K Y h = 1)
    (hm : m ≠ 0) (α β : ℝ) :
    tick C K X h (α • v, β • v) = ((α - h ^ 2 * κ * α / m) • v, (-2 * h * κ * α / m - β) • v) := by
  have h1 : X *ᵥ (operator C D K Y h *ᵥ v) = v := by
    rw [mulVec_mulVec, hX, one_mulVec]
  rw [hM, mulVec_smul] at h1
  have hXv : X *ᵥ v = m⁻¹ • v := by
    calc X *ᵥ v = m⁻¹ • (m • X *ᵥ v) := by rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
      _ = m⁻¹ • v := by rw [h1]
  have hr : (2 : ℝ) • (C *ᵥ (β • v)) - h • (K *ᵥ (α • v)) = (-(h * κ * α)) • v := by
    rw [mulVec_smul, mulVec_smul, hC, hK]
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    ring
  unfold tick
  simp only
  rw [hr, mulVec_smul, hXv]
  refine Prod.ext ?_ ?_
  · ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  · ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- [proved-derived] The first coefficient of the two ticks returns: `u″ = u`. -/
theorem shear_first {a h p : ℝ} (hab : a - h ^ 2 * p ≠ 0) (hab' : a + h ^ 2 * p ≠ 0) (α : ℝ) :
    α - h ^ 2 * (-2 * p) * α / (a - h ^ 2 * p) -
        h ^ 2 * (2 * p) * (α - h ^ 2 * (-2 * p) * α / (a - h ^ 2 * p)) / (a + h ^ 2 * p) = α := by
  field_simp
  ring

/-- [proved-derived] The second coefficient of the two ticks takes the shear: `w″ = w − 8hpu/(a − b)`. -/
theorem shear_second {a h p : ℝ} (hab : a - h ^ 2 * p ≠ 0) (hab' : a + h ^ 2 * p ≠ 0) (α β : ℝ) :
    -2 * h * (2 * p) * (α - h ^ 2 * (-2 * p) * α / (a - h ^ 2 * p)) / (a + h ^ 2 * p) -
        (-2 * h * (-2 * p) * α / (a - h ^ 2 * p) - β) = β - 8 * h * p * α / (a - h ^ 2 * p) := by
  field_simp
  ring

/-- [proved-derived; formal-checked] **The Half pump's period map on the harmonic in-phase pair is a shear**: with
`a = h/Y + hd`, `b = h²p`, `C v = K v = 0`, `D v = d v`, the pump's in-phase reading `P v = −2p v`, the two phases
`K + P` and `K − P` and their executed solves, `T₁T₀ (αv, βv) = (αv, (β − 8hpα/(a − b)) v)`. -/
theorem half_pump_harmonic_monodromy {C D K P X₀ X₁ : Matrix ι ι ℝ} {Y h d p : ℝ} {v : ι → ℝ}
    (hC : C *ᵥ v = 0) (hK : K *ᵥ v = 0) (hD : D *ᵥ v = d • v) (hP : P *ᵥ v = (-2 * p) • v)
    (hX₀ : X₀ * operator C D (K + P) Y h = 1) (hX₁ : X₁ * operator C D (K - P) Y h = 1)
    (hab : h / Y + h * d - h ^ 2 * p ≠ 0) (hab' : h / Y + h * d + h ^ 2 * p ≠ 0) (α β : ℝ) :
    tick C (K - P) X₁ h (tick C (K + P) X₀ h (α • v, β • v)) =
      (α • v, (β - 8 * h * p * α / (h / Y + h * d - h ^ 2 * p)) • v) := by
  have hK₀ : (K + P) *ᵥ v = (-2 * p) • v := by rw [add_mulVec, hK, hP, zero_add]
  have hK₁ : (K - P) *ᵥ v = (2 * p) • v := by
    rw [sub_mulVec, hK, hP, zero_sub, ← neg_smul]
    congr 1
    ring
  have hM₀ := operator_harmonic (Y := Y) (h := h) hC hD hK₀
  have hM₁ := operator_harmonic (Y := Y) (h := h) hC hD hK₁
  have hm₀ : h / Y + h * d + h ^ 2 / 2 * (-2 * p) = h / Y + h * d - h ^ 2 * p := by ring
  have hm₁ : h / Y + h * d + h ^ 2 / 2 * (2 * p) = h / Y + h * d + h ^ 2 * p := by ring
  rw [hm₀] at hM₀
  rw [hm₁] at hM₁
  rw [tick_harmonic hC hK₀ hM₀ hX₀ hab α β, tick_harmonic hC hK₁ hM₁ hX₁ hab']
  congr 2
  · exact shear_first hab hab' α
  · exact shear_second hab hab' α β

/-- [definition] **The harmonic shear** `[[1, 0], [−8hp/(a − b), 1]]`. -/
noncomputable def shear (h p a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; -8 * h * p / (a - b), 1]

/-- [proved-derived] The shear's determinant is one. -/
theorem shear_det (h p a b : ℝ) : (shear h p a b).det = 1 := by
  unfold shear
  rw [Matrix.det_fin_two_of]
  ring

/-- [proved-derived] The shear's trace is two: both multipliers are one. -/
theorem shear_trace (h p a b : ℝ) : (shear h p a b).trace = 2 := by
  unfold shear
  rw [Matrix.trace_fin_two_of]
  norm_num

/-- [proved-derived; formal-checked] **The monodromy in the coordinates of the pair**: the two ticks act on the
coefficients `(α, β)` of `(αv, βv)` by the shear. -/
theorem half_pump_harmonic_monodromy_matrix {C D K P X₀ X₁ : Matrix ι ι ℝ} {Y h d p : ℝ} {v : ι → ℝ}
    (hC : C *ᵥ v = 0) (hK : K *ᵥ v = 0) (hD : D *ᵥ v = d • v) (hP : P *ᵥ v = (-2 * p) • v)
    (hX₀ : X₀ * operator C D (K + P) Y h = 1) (hX₁ : X₁ * operator C D (K - P) Y h = 1)
    (hab : h / Y + h * d - h ^ 2 * p ≠ 0) (hab' : h / Y + h * d + h ^ 2 * p ≠ 0) (α β : ℝ) :
    let c := shear h p (h / Y + h * d) (h ^ 2 * p) *ᵥ ![α, β]
    tick C (K - P) X₁ h (tick C (K + P) X₀ h (α • v, β • v)) = (c 0 • v, c 1 • v) := by
  intro c
  rw [half_pump_harmonic_monodromy hC hK hD hP hX₀ hX₁ hab hab' α β]
  have h0 : c 0 = α := by
    simp [c, shear]
  have h1 : c 1 = β - 8 * h * p * α / (h / Y + h * d - h ^ 2 * p) := by
    simp only [c, shear, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [h0, h1]

end Tick

/-! ## 2. The signed form and its edge -/

section Form

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The signed form** `2C + hD + (h²/2) K` of one pump phase. -/
noncomputable def signedForm (C D K : Matrix ι ι ℝ) (h : ℝ) : Matrix ι ι ℝ := (2 : ℝ) • C + h • D + (h ^ 2 / 2) • K

/-- [definition] **The Half pump's certificate**: both phases' signed forms are positive semidefinite. -/
def Certifies (C D K P : Matrix ι ι ℝ) (h : ℝ) : Prop :=
  ∀ z : ι → ℝ, 0 ≤ z ⬝ᵥ (signedForm C D (K + P) h *ᵥ z) ∧ 0 ≤ z ⬝ᵥ (signedForm C D (K - P) h *ᵥ z)

omit [DecidableEq ι] in
/-- [proved-standard] The signed form's quadratic value is the sum of its parts'. -/
theorem signedForm_quadratic (C D K : Matrix ι ι ℝ) (h : ℝ) (z : ι → ℝ) :
    z ⬝ᵥ (signedForm C D K h *ᵥ z) =
      2 * (z ⬝ᵥ (C *ᵥ z)) + h * (z ⬝ᵥ (D *ᵥ z)) + h ^ 2 / 2 * (z ⬝ᵥ (K *ᵥ z)) := by
  unfold signedForm
  simp only [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

/-- [proved-standard] The operator's quadratic value is the signed form's and the port's `(h/Y)|z|²`. -/
theorem operator_quadratic (C D K : Matrix ι ι ℝ) (Y h : ℝ) (z : ι → ℝ) :
    z ⬝ᵥ (operator C D K Y h *ᵥ z) = z ⬝ᵥ (signedForm C D K h *ᵥ z) + h / Y * (z ⬝ᵥ z) := by
  rw [signedForm_quadratic]
  unfold operator
  simp only [add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  ring

omit [DecidableEq ι] in
/-- [proved-standard] `|z|² ≥ 0`. -/
theorem dotProduct_self_nonneg' (z : ι → ℝ) : 0 ≤ z ⬝ᵥ z :=
  Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))

/-- [proved-derived; formal-checked] **The Half pump's signed form certifies iff `p ≤ d/h`**: with `C, K ⪰ 0`,
`D = dI`, the pump bounded by its strength and a harmonic vector `v ≠ 0` with `C v = K v = 0` on which the pump reads
`−2p`, both phases certify exactly when `p ≤ d/h`. -/
theorem half_pump_edge_certifies {C D K P : Matrix ι ι ℝ} {h d p : ℝ} {v : ι → ℝ}
    (hC : ∀ z, 0 ≤ z ⬝ᵥ (C *ᵥ z)) (hK : ∀ z, 0 ≤ z ⬝ᵥ (K *ᵥ z)) (hD : D = d • (1 : Matrix ι ι ℝ))
    (hPb : ∀ z, |z ⬝ᵥ (P *ᵥ z)| ≤ 2 * p * (z ⬝ᵥ z)) (hv : v ≠ 0) (hCv : C *ᵥ v = 0) (hKv : K *ᵥ v = 0)
    (hPv : P *ᵥ v = (-2 * p) • v) (hh : 0 < h) :
    Certifies C D K P h ↔ p ≤ d / h := by
  have hDq : ∀ z, z ⬝ᵥ (D *ᵥ z) = d * (z ⬝ᵥ z) := by
    intro z
    rw [hD, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  rw [le_div_iff₀ hh]
  constructor
  · intro hcert
    have h0 := (hcert v).1
    rw [signedForm_quadratic, hCv, hDq, add_mulVec, hKv, hPv, zero_add, dotProduct_zero, dotProduct_smul,
      smul_eq_mul] at h0
    have hvv : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg' v)
      (fun h' => hv (dotProduct_self_eq_zero.mp h'.symm))
    have : 0 ≤ h * (d - h * p) * (v ⬝ᵥ v) := by nlinarith
    have h2 : 0 ≤ h * (d - h * p) := nonneg_of_mul_nonneg_left this hvv
    have h3 : 0 ≤ d - h * p := nonneg_of_mul_nonneg_right (by linarith) hh
    nlinarith
  · intro hp z
    have hzz := dotProduct_self_nonneg' z
    have hb := hPb z
    have hlo := neg_abs_le (z ⬝ᵥ (P *ᵥ z))
    have hhi := le_abs_self (z ⬝ᵥ (P *ᵥ z))
    have hCz := hC z
    have hKz := hK z
    have hdp : 0 ≤ h * (d - h * p) * (z ⬝ᵥ z) := mul_nonneg (mul_nonneg hh.le (by linarith)) hzz
    have hh2 : 0 ≤ h ^ 2 / 2 := by positivity
    constructor
    · rw [signedForm_quadratic, hDq, add_mulVec, dotProduct_add]
      nlinarith [mul_le_mul_of_nonneg_left (show -(2 * p * (z ⬝ᵥ z)) ≤ z ⬝ᵥ (P *ᵥ z) by linarith) hh2]
    · rw [signedForm_quadratic, hDq, sub_mulVec, dotProduct_sub]
      nlinarith [mul_le_mul_of_nonneg_left (show z ⬝ᵥ (P *ᵥ z) ≤ 2 * p * (z ⬝ᵥ z) by linarith) hh2]

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **At the edge the form is singular**: at `hp = d` the first phase's signed form
sends the harmonic vector to zero. -/
theorem half_pump_edge_singular {C D K P : Matrix ι ι ℝ} {h d p : ℝ} {v : ι → ℝ} (hD : D *ᵥ v = d • v)
    (hCv : C *ᵥ v = 0) (hKv : K *ᵥ v = 0) (hPv : P *ᵥ v = (-2 * p) • v) (hedge : h * p = d) :
    signedForm C D (K + P) h *ᵥ v = 0 := by
  unfold signedForm
  simp only [add_mulVec, smul_mulVec, hCv, hD, hKv, hPv, zero_add, smul_zero]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  rw [← hedge]
  ring

/-- [proved-derived; formal-checked] **A certified phase solves uniquely**: where the signed form is positive
semidefinite and `h/Y > 0`, the operator is invertible. -/
theorem operator_det_ne_zero {C D K : Matrix ι ι ℝ} {Y h : ℝ} (hhY : 0 < h / Y)
    (hS : ∀ z, 0 ≤ z ⬝ᵥ (signedForm C D K h *ᵥ z)) : (operator C D K Y h).det ≠ 0 := by
  intro hdet
  obtain ⟨z, hz, hMz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hq := operator_quadratic C D K Y h z
  rw [hMz, dotProduct_zero] at hq
  have hS' := hS z
  have hzz := dotProduct_self_nonneg' z
  have : z ⬝ᵥ z = 0 := by nlinarith
  exact hz (dotProduct_self_eq_zero.mp this)

/-- [proved-derived; formal-checked] **The certified Half pump's monodromy**: under the hypotheses of the edge theorem,
`Y > 0` and `p ≤ d/h`, both phases' inverses are executed solves and the period map on the harmonic in-phase pair is
the shear. -/
theorem half_pump_certified_monodromy {C D K P : Matrix ι ι ℝ} {Y h d p : ℝ} {v : ι → ℝ}
    (hC : ∀ z, 0 ≤ z ⬝ᵥ (C *ᵥ z)) (hK : ∀ z, 0 ≤ z ⬝ᵥ (K *ᵥ z)) (hD : D = d • (1 : Matrix ι ι ℝ))
    (hPb : ∀ z, |z ⬝ᵥ (P *ᵥ z)| ≤ 2 * p * (z ⬝ᵥ z)) (hv : v ≠ 0) (hCv : C *ᵥ v = 0) (hKv : K *ᵥ v = 0)
    (hPv : P *ᵥ v = (-2 * p) • v) (hh : 0 < h) (hY : 0 < Y) (hp : p ≤ d / h) (α β : ℝ) :
    tick C (K - P) (operator C D (K - P) Y h)⁻¹ h (tick C (K + P) (operator C D (K + P) Y h)⁻¹ h (α • v, β • v)) =
      (α • v, (β - 8 * h * p * α / (h / Y + h * d - h ^ 2 * p)) • v) := by
  have hcert := (half_pump_edge_certifies hC hK hD hPb hv hCv hKv hPv hh).mpr hp
  have hhY : 0 < h / Y := div_pos hh hY
  have hdet₀ := operator_det_ne_zero (Y := Y) hhY (fun z => (hcert z).1)
  have hdet₁ := operator_det_ne_zero (Y := Y) hhY (fun z => (hcert z).2)
  have hDv : D *ᵥ v = d • v := by rw [hD, smul_mulVec, one_mulVec]
  have hp' : h * p ≤ d := by rwa [le_div_iff₀ hh, mul_comm] at hp
  have hvv : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg' v)
    (fun h' => hv (dotProduct_self_eq_zero.mp h'.symm))
  have hp0 : 0 ≤ p := by
    have := hPb v
    rw [hPv, dotProduct_smul, smul_eq_mul, abs_mul] at this
    have habs : |v ⬝ᵥ v| = v ⬝ᵥ v := abs_of_pos hvv
    rw [habs] at this
    have : |(-2 * p)| ≤ 2 * p := le_of_mul_le_mul_right (by linarith) hvv
    linarith [abs_nonneg (-2 * p)]
  have hab : h / Y + h * d - h ^ 2 * p ≠ 0 := by
    have : h ^ 2 * p ≤ h * d := by nlinarith
    linarith
  have hab' : h / Y + h * d + h ^ 2 * p ≠ 0 := by
    have : 0 ≤ h ^ 2 * p := by positivity
    have : 0 ≤ h * d := by nlinarith
    linarith
  exact half_pump_harmonic_monodromy (hCv) hKv hDv hPv (nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet₀))
    (nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet₁)) hab hab' α β

end Form

/-! ## 3. The ring the Rust declares -/

section Cyclic

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- [definition] **The cyclic incidence** `(Bx)_i = x_(i+1) − x_i` on `Fin n`. -/
def cyclicIncidence (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (if j = finRotate n i then 1 else 0) - (if j = i then 1 else 0)

/-- [proved-standard] **The harmonic vector is the incidence's kernel**: `B·1 = 0`. -/
theorem cyclicIncidence_harmonic (n : ℕ) : cyclicIncidence n *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext i
  simp [cyclicIncidence, Matrix.mulVec, dotProduct, Finset.sum_sub_distrib]

/-- [definition] **A weighted form** `BᵀWB`. -/
def weightedForm (B : Matrix N N ℝ) (w : N → ℝ) : Matrix N N ℝ := Bᵀ * Matrix.diagonal w * B

/-- [proved-standard] A weighted form keeps the incidence's harmonic kernel. -/
theorem weightedForm_harmonic {B : Matrix N N ℝ} (hB : B *ᵥ (fun _ => (1 : ℝ)) = 0) (w : N → ℝ) :
    weightedForm B w *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  unfold weightedForm
  rw [← mulVec_mulVec, hB, mulVec_zero]

/-- [proved-standard] A weighted form with nonnegative weights is positive semidefinite: `⟨z, BᵀWBz⟩ = Σ w (Bz)²`. -/
theorem weightedForm_nonneg (B : Matrix N N ℝ) {w : N → ℝ} (hw : ∀ i, 0 ≤ w i) (z : N → ℝ) :
    0 ≤ z ⬝ᵥ (weightedForm B w *ᵥ z) := by
  unfold weightedForm
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  unfold dotProduct
  refine Finset.sum_nonneg (fun i _ => ?_)
  rw [mulVec_diagonal]
  nlinarith [mul_self_nonneg ((B *ᵥ z) i), hw i]

/-- [definition] **The realified form** on the two coordinates of every node, as two blocks. -/
def realify (A : Matrix N N ℝ) : Matrix (N ⊕ N) (N ⊕ N) ℝ := Matrix.fromBlocks A 0 0 A

/-- [definition] **The Half pump's node block on its phase-zero axis**, `−2p [[1, 0], [0, −1]]` at every node. -/
def phaseZeroPump (p : ℝ) : Matrix (N ⊕ N) (N ⊕ N) ℝ :=
  Matrix.fromBlocks ((-2 * p) • (1 : Matrix N N ℝ)) 0 0 ((2 * p) • (1 : Matrix N N ℝ))

/-- [definition] **The harmonic in-phase vector**: real part one at every node, imaginary part zero. -/
def harmonicInPhase : N ⊕ N → ℝ := Sum.elim (fun _ => 1) (fun _ => 0)

omit [DecidableEq N] in
/-- [proved-standard] A pairing on the two blocks is the sum of the blocks' pairings. -/
theorem dotProduct_sum (x y : N ⊕ N → ℝ) :
    x ⬝ᵥ y = (x ∘ Sum.inl) ⬝ᵥ (y ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ (y ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq N] in
/-- [proved-standard] The realified form's quadratic value is the two coordinates'. -/
theorem realify_quadratic (A : Matrix N N ℝ) (z : N ⊕ N → ℝ) :
    z ⬝ᵥ (realify A *ᵥ z) = (z ∘ Sum.inl) ⬝ᵥ (A *ᵥ (z ∘ Sum.inl)) + (z ∘ Sum.inr) ⬝ᵥ (A *ᵥ (z ∘ Sum.inr)) := by
  rw [dotProduct_sum]
  unfold realify
  rw [fromBlocks_mulVec]
  simp [Matrix.zero_mulVec]

omit [Fintype N] [DecidableEq N] in
/-- [proved-standard] The in-phase vector's real part is one at every node. -/
theorem harmonicInPhase_inl : (harmonicInPhase : N ⊕ N → ℝ) ∘ Sum.inl = fun _ => 1 := rfl

omit [Fintype N] [DecidableEq N] in
/-- [proved-standard] Its imaginary part is zero. -/
theorem harmonicInPhase_inr : (harmonicInPhase : N ⊕ N → ℝ) ∘ Sum.inr = 0 := rfl

omit [DecidableEq N] in
/-- [proved-standard] The realified form keeps a harmonic vector of its block on the real coordinate. -/
theorem realify_harmonic {A : Matrix N N ℝ} (hA : A *ᵥ (fun _ => (1 : ℝ)) = 0) :
    realify A *ᵥ harmonicInPhase = 0 := by
  unfold realify
  rw [fromBlocks_mulVec, harmonicInPhase_inl, harmonicInPhase_inr, hA]
  simp only [mulVec_zero, zero_mulVec, add_zero]
  ext i
  cases i <;> simp

/-- [proved-standard] **The pump reads `−2p` on the in-phase sheet.** -/
theorem phaseZeroPump_harmonic (p : ℝ) :
    phaseZeroPump (N := N) p *ᵥ harmonicInPhase = (-2 * p) • harmonicInPhase := by
  unfold phaseZeroPump
  rw [fromBlocks_mulVec, harmonicInPhase_inl, harmonicInPhase_inr, smul_mulVec, smul_mulVec, one_mulVec,
    one_mulVec, zero_mulVec, zero_mulVec]
  ext i
  cases i <;> simp [harmonicInPhase]

/-- [proved-standard] **The pump is bounded by its strength**: `|⟨z, P z⟩| ≤ 2p|z|²` for `p ≥ 0`. -/
theorem phaseZeroPump_bound {p : ℝ} (hp : 0 ≤ p) (z : N ⊕ N → ℝ) :
    |z ⬝ᵥ (phaseZeroPump p *ᵥ z)| ≤ 2 * p * (z ⬝ᵥ z) := by
  have hq : z ⬝ᵥ (phaseZeroPump p *ᵥ z) =
      -2 * p * ((z ∘ Sum.inl) ⬝ᵥ (z ∘ Sum.inl)) + 2 * p * ((z ∘ Sum.inr) ⬝ᵥ (z ∘ Sum.inr)) := by
    rw [dotProduct_sum]
    unfold phaseZeroPump
    rw [fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_mulVec, add_zero, zero_add,
      smul_mulVec, smul_mulVec, one_mulVec, one_mulVec, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hq, dotProduct_sum]
  have hx := dotProduct_self_nonneg' (z ∘ Sum.inl)
  have hy := dotProduct_self_nonneg' (z ∘ Sum.inr)
  rw [abs_le]
  constructor <;> nlinarith

omit [Fintype N] [DecidableEq N] in
/-- [proved-standard] On nonempty nodes the in-phase vector is not zero. -/
theorem harmonicInPhase_ne_zero [Nonempty N] : (harmonicInPhase : N ⊕ N → ℝ) ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty N›
  have := congrFun h (Sum.inl i)
  simp [harmonicInPhase] at this

/-- [proved-standard] A realified weighted form with nonnegative weights is positive semidefinite. -/
theorem realify_nonneg (B : Matrix N N ℝ) {w : N → ℝ} (hw : ∀ i, 0 ≤ w i) (z : N ⊕ N → ℝ) :
    0 ≤ z ⬝ᵥ (realify (weightedForm B w) *ᵥ z) := by
  rw [realify_quadratic]
  exact add_nonneg (weightedForm_nonneg B hw _) (weightedForm_nonneg B hw _)

/-- [proved-derived; formal-checked] **On the declared ring the Half pump certifies iff `p ≤ d/h`**: any incidence
with `B·1 = 0` (the cyclic one, `cyclicIncidence_harmonic`) and nonempty nodes, nonnegative weights, `D = dI`,
`p ≥ 0` and `h > 0`. -/
theorem cyclic_half_pump_edge_certifies [Nonempty N] {B : Matrix N N ℝ} (hB : B *ᵥ (fun _ => (1 : ℝ)) = 0)
    {wC wK : N → ℝ} (hwC : ∀ i, 0 ≤ wC i) (hwK : ∀ i, 0 ≤ wK i) {h d p : ℝ} (hp : 0 ≤ p) (hh : 0 < h) :
    Certifies (realify (weightedForm B wC)) (d • (1 : Matrix (N ⊕ N) (N ⊕ N) ℝ)) (realify (weightedForm B wK))
      (phaseZeroPump p) h ↔ p ≤ d / h :=
  half_pump_edge_certifies (realify_nonneg B hwC) (realify_nonneg B hwK) rfl (phaseZeroPump_bound hp)
    harmonicInPhase_ne_zero (realify_harmonic (weightedForm_harmonic hB wC))
    (realify_harmonic (weightedForm_harmonic hB wK)) (phaseZeroPump_harmonic p) hh

/-- [proved-derived; formal-checked] **On the declared ring the certified Half pump holds the harmonic in-phase pair on
the shear** `[[1, 0], [−8hp/(a − b), 1]]`, `a = h/Y + hd`, `b = h²p`. -/
theorem cyclic_half_pump_monodromy [Nonempty N] {B : Matrix N N ℝ} (hB : B *ᵥ (fun _ => (1 : ℝ)) = 0)
    {wC wK : N → ℝ} (hwC : ∀ i, 0 ≤ wC i) (hwK : ∀ i, 0 ≤ wK i) {Y h d p : ℝ} (hp0 : 0 ≤ p) (hh : 0 < h)
    (hY : 0 < Y) (hp : p ≤ d / h) (α β : ℝ) :
    let C := realify (weightedForm B wC)
    let K := realify (weightedForm B wK)
    let D := d • (1 : Matrix (N ⊕ N) (N ⊕ N) ℝ)
    let P := phaseZeroPump (N := N) p
    tick C (K - P) (operator C D (K - P) Y h)⁻¹ h
        (tick C (K + P) (operator C D (K + P) Y h)⁻¹ h (α • harmonicInPhase, β • harmonicInPhase)) =
      (α • harmonicInPhase, (β - 8 * h * p * α / (h / Y + h * d - h ^ 2 * p)) • harmonicInPhase) :=
  half_pump_certified_monodromy (realify_nonneg B hwC) (realify_nonneg B hwK) rfl (phaseZeroPump_bound hp0)
    harmonicInPhase_ne_zero (realify_harmonic (weightedForm_harmonic hB wC))
    (realify_harmonic (weightedForm_harmonic hB wK)) (phaseZeroPump_harmonic p) hh hY hp α β

end Cyclic

/-! ## 4. The declared cases -/

/-- [proved-derived] **The entries the Rust test fixes**, `−8hp/(a − b)` with `a = h/Y + h/Y` (`d = 1/Y`) and
`b = h²p`: `(2, 1, 1/2) ↦ −8`, `(2, 1, 1/4) ↦ −8/3`, `(3, 2, 1/6) ↦ −4`, `(3, 2, 1/12) ↦ −4/3`. -/
theorem declared_entries :
    -8 * (1 : ℝ) * (1 / 2) / (1 / 2 + 1 * (1 / 2) - 1 ^ 2 * (1 / 2)) = -8 ∧
    -8 * (1 : ℝ) * (1 / 4) / (1 / 2 + 1 * (1 / 2) - 1 ^ 2 * (1 / 4)) = -8 / 3 ∧
    -8 * (2 : ℝ) * (1 / 6) / (2 / 3 + 2 * (1 / 3) - 2 ^ 2 * (1 / 6)) = -4 ∧
    -8 * (2 : ℝ) * (1 / 12) / (2 / 3 + 2 * (1 / 3) - 2 ^ 2 * (1 / 12)) = -4 / 3 := by
  norm_num

/-- [proved-derived] **The declared cases against the edge `d/h`**: the four certified strengths stand at or under it,
`p = d/h` at `1/2` and `1/6`; the four refused ones stand past it (`65/128` and `1` at `d/h = 1/2`, `65/384` and `1/3`
at `d/h = 1/6`), the second of each pair at the shear's singularity `2d/h`. -/
theorem declared_edges :
    ((1 : ℝ) / 2 ≤ (1 / 2) / 1 ∧ (1 : ℝ) / 4 ≤ (1 / 2) / 1 ∧ (1 : ℝ) / 6 ≤ (1 / 3) / 2 ∧ (1 : ℝ) / 12 ≤ (1 / 3) / 2) ∧
    ((1 / 2) / 1 < (65 : ℝ) / 128 ∧ (1 / 2) / 1 < (1 : ℝ) ∧ (1 / 3) / 2 < (65 : ℝ) / 384 ∧ (1 / 3) / 2 < (1 : ℝ) / 3) ∧
    ((1 : ℝ) / 2 + 1 * (1 / 2) = 1 ^ 2 * 1 ∧ (2 : ℝ) / 3 + 2 * (1 / 3) = 2 ^ 2 * (1 / 3)) := by
  norm_num

end Holonics.HNN.HalfPumpMonodromy
