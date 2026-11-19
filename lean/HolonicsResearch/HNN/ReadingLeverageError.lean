import Mathlib

/-!
# The fitted form's error at a new reading: `σ² (1 + h)` in range, whatever the true form

`HNN/ReadingLeverage` reads a new reading's leverage `h` against the encounter Gram `G = XᵀX` and proves it chart-free
in range, `h = vᵀ G⁻ v` for every generalized inverse (`chartLeverage_eq_ginv`). #410's box also asks for what the
leverage predicts: if each cell's arrival is a form's value plus noise of variance `σ²`, the fitted form's mean square
error at a new reading in range is `σ² (1 + h)`, whatever the true form `w*`; out of range it adds
`(vᵀ (I − G⁻ G) w*)²`, which the cells do not fix (record
`2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT`,
§10; atlas `contact.reading-leverage`).

[proved-derived; formal-checked] What is proved, over ℝ, on any probability space, for cells `ι` with readings the rows
of `X`, the Gram `G = XᵀX`, any generalized inverse `G⁻` (`G G⁻ G = G`), a true form `w`, arrivals
`y_t = ⟨x_t, w⟩ + e_t`, the fitted form `ŵ = G⁻ Xᵀ y`, and a new reading `v` arriving as `⟨v, w⟩ + e₀`, where the
noises `e₀, e_t` are white: centred, with `E[e_s e_t] = σ² [s = t]`.

1. **A white combination** (`integral_white_sq`): `E[(β + Σ_s c_s e_s)²] = β² + σ² Σ_s c_s²`.
2. **The error splits** (`error_eq`): the error `⟨v, w⟩ + e₀ − ⟨v, ŵ⟩` is the bias `⟨v, w⟩ − ⟨v, G⁻ G w⟩` plus the
   noise `e₀ − ⟨X G⁻ᵀ v, e⟩`.
3. **Its mean square** (`meanSquare_error`): `E[error²] = (⟨v, w⟩ − ⟨v, G⁻ G w⟩)² + σ² (1 + |X G⁻ᵀ v|²)`.
4. **In range** (`meanSquare_error_of_mem_range`, through `range_identities`): for `v = G u` the bias vanishes for
   every true form `w`, and `|X G⁻ᵀ v|² = uᵀ G u = vᵀ G⁻ v = h`, so `E[error²] = σ² (1 + h)`.

The computational object is the helical pair interaction's encounter Gram: the cells a contact has met, the form the
contact fits on them, and what that form costs at a reading it has not met. Of the winding guide's six general
objects this touches faces and placement (the reading's chart); the helix, the pair, the cell holonomy, the tube and
the tower thread stay attached.

What stands beside it: `HNN/ReadingLeverage` (the split, `chartLeverage_eq_ginv`, the prequential identities) and
`HNN/ReadingLeverageSeries` (the leverage as a series over the pivots). The charge `½ log₂ (1 + h)` of the Gaussian
chart and the off-range limit `ε vᵀ (G + ε I)⁻¹ v → |(I − G G⁺) v|²` are not stated.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReadingLeverageError

open MeasureTheory Matrix Finset

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- [definition] **White noise** of variance `σ²`: centred, its products integrable, `E[e_s e_t] = σ² [s = t]`. -/
structure White (e : Ω → κ → ℝ) (σ2 : ℝ) : Prop where
  integrable : ∀ s, Integrable (fun ω => e ω s) μ
  centred : ∀ s, ∫ ω, e ω s ∂μ = 0
  integrable_mul : ∀ s t, Integrable (fun ω => e ω s * e ω t) μ
  cov : ∀ s t, ∫ ω, e ω s * e ω t ∂μ = if s = t then σ2 else 0

variable {μ}

/-- **A white combination**: `E[(β + Σ_s c_s e_s)²] = β² + σ² Σ_s c_s²`. -/
theorem integral_white_sq [IsProbabilityMeasure μ] {e : Ω → κ → ℝ} {σ2 : ℝ} (hw : White μ e σ2) (β : ℝ)
    (c : κ → ℝ) :
    ∫ ω, (β + ∑ s, c s * e ω s) ^ 2 ∂μ = β ^ 2 + σ2 * ∑ s, c s ^ 2 := by
  have hexp : ∀ ω, (β + ∑ s, c s * e ω s) ^ 2 =
      β ^ 2 + (∑ s, (2 * β * c s) * e ω s + ∑ s, ∑ t, (c s * c t) * (e ω s * e ω t)) := by
    intro ω
    have h1 : (∑ s, c s * e ω s) ^ 2 = ∑ s, ∑ t, (c s * c t) * (e ω s * e ω t) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      ring
    have h2 : ∑ s, (2 * β * c s) * e ω s = 2 * β * ∑ s, c s * e ω s := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    rw [h2, ← h1]
    ring
  simp_rw [hexp]
  have hi1 : Integrable (fun ω => ∑ s, (2 * β * c s) * e ω s) μ :=
    integrable_finsetSum _ fun s _ => (hw.integrable s).const_mul _
  have hi2 : Integrable (fun ω => ∑ s, ∑ t, (c s * c t) * (e ω s * e ω t)) μ :=
    integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun t _ => (hw.integrable_mul s t).const_mul _
  have hi12 : Integrable (fun ω => ∑ s, (2 * β * c s) * e ω s + ∑ s, ∑ t, (c s * c t) * (e ω s * e ω t)) μ :=
    hi1.add hi2
  rw [integral_add (integrable_const _) hi12, integral_add hi1 hi2,
    integral_finsetSum _ fun s _ => (hw.integrable s).const_mul _,
    integral_finsetSum _ fun s _ => integrable_finsetSum _ fun t _ => (hw.integrable_mul s t).const_mul _]
  have hin : ∀ s, ∫ ω, ∑ t, (c s * c t) * (e ω s * e ω t) ∂μ = σ2 * c s ^ 2 := fun s => by
    rw [integral_finsetSum _ fun t _ => (hw.integrable_mul s t).const_mul _]
    simp only [integral_const_mul, hw.cov, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp only [integral_const_mul, hw.centred, mul_zero, Finset.sum_const_zero, zero_add, hin, ← Finset.mul_sum]
  rw [integral_const]
  simp

/-! ## The fitted form's error -/

section Fit

variable {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n]

/-- [definition] The fitted form `ŵ = G⁻ Xᵀ y` from the arrivals `y_t = ⟨x_t, w⟩ + e_t`. -/
noncomputable def fitted (X : Matrix ι n ℝ) (Gm : Matrix n n ℝ) (w : n → ℝ) (e : Option ι → ℝ) : n → ℝ :=
  Gm *ᵥ (Xᵀ *ᵥ (X *ᵥ w + fun t => e (some t)))

/-- [definition] The error at a new reading `v` arriving as `⟨v, w⟩ + e₀`. -/
noncomputable def error (X : Matrix ι n ℝ) (Gm : Matrix n n ℝ) (w : n → ℝ) (e : Option ι → ℝ) (v : n → ℝ) : ℝ :=
  (v ⬝ᵥ w + e none) - v ⬝ᵥ fitted X Gm w e

/-- [definition] The noise's weights in the error: `1` on the new arrival, `−(X G⁻ᵀ v)_t` on the cells. -/
noncomputable def weights (X : Matrix ι n ℝ) (Gm : Matrix n n ℝ) (v : n → ℝ) : Option ι → ℝ :=
  fun s => Option.elim s 1 fun t => -(X *ᵥ (Gmᵀ *ᵥ v)) t

omit [DecidableEq ι] in
/-- **The error splits** into the bias `⟨v, w⟩ − ⟨v, G⁻ G w⟩` and a combination of the noises. -/
theorem error_eq (X : Matrix ι n ℝ) (Gm : Matrix n n ℝ) (w : n → ℝ) (e : Option ι → ℝ) (v : n → ℝ) :
    error X Gm w e v = (v ⬝ᵥ w - v ⬝ᵥ (Gm *ᵥ ((Xᵀ * X) *ᵥ w))) + ∑ s, weights X Gm v s * e s := by
  have hsplit : v ⬝ᵥ (Gm *ᵥ (Xᵀ *ᵥ fun t => e (some t))) = (X *ᵥ (Gmᵀ *ᵥ v)) ⬝ᵥ fun t => e (some t) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_mulVec, vecMul_transpose]
  simp only [error, fitted, mulVec_add, dotProduct_add, ← mulVec_mulVec]
  rw [hsplit]
  simp only [Fintype.sum_option, weights, Option.elim, one_mul, neg_mul, Finset.sum_neg_distrib, dotProduct]
  ring

/-- **Its mean square**: `E[error²] = bias² + σ² (1 + |X G⁻ᵀ v|²)`. -/
theorem meanSquare_error [IsProbabilityMeasure μ] {e : Ω → Option ι → ℝ} {σ2 : ℝ} (hw : White μ e σ2)
    (X : Matrix ι n ℝ) (Gm : Matrix n n ℝ) (w v : n → ℝ) :
    ∫ ω, error X Gm w (e ω) v ^ 2 ∂μ =
      (v ⬝ᵥ w - v ⬝ᵥ (Gm *ᵥ ((Xᵀ * X) *ᵥ w))) ^ 2 +
        σ2 * (1 + (X *ᵥ (Gmᵀ *ᵥ v)) ⬝ᵥ (X *ᵥ (Gmᵀ *ᵥ v))) := by
  simp_rw [error_eq]
  rw [integral_white_sq hw]
  congr 2
  simp only [Fintype.sum_option, weights, Option.elim, neg_mul_neg, mul_one, dotProduct, sq]

omit [DecidableEq ι] [Fintype n] in
theorem gram_symm (X : Matrix ι n ℝ) : (Xᵀ * X)ᵀ = Xᵀ * X := by
  rw [transpose_mul, transpose_transpose]

omit [DecidableEq ι] [Fintype ι] in
/-- In range, for a symmetric `G` and any generalized inverse: `vᵀ G⁻ v = uᵀ G u` at `v = G u`, the bias vanishes,
and `G G⁻ᵀ G = G`. -/
theorem range_identities {G Gm : Matrix n n ℝ} (hsym : Gᵀ = G) (hGm : G * Gm * G = G) (u w : n → ℝ) :
    (G *ᵥ u) ⬝ᵥ (Gm *ᵥ (G *ᵥ u)) = u ⬝ᵥ (G *ᵥ u) ∧
      (G *ᵥ u) ⬝ᵥ w - (G *ᵥ u) ⬝ᵥ (Gm *ᵥ (G *ᵥ w)) = 0 ∧ G * Gmᵀ * G = G := by
  have hmove : ∀ a b : n → ℝ, (G *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (G *ᵥ b) := fun a b => by
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  refine ⟨?_, ?_, ?_⟩
  · rw [hmove, mulVec_mulVec, mulVec_mulVec, hGm]
  · rw [hmove u w, hmove u (Gm *ᵥ (G *ᵥ w)), mulVec_mulVec, mulVec_mulVec, hGm, sub_self]
  · have h := congrArg Matrix.transpose hGm
    rwa [transpose_mul, transpose_mul, hsym, ← Matrix.mul_assoc] at h

/-- **In range the mean square error is `σ² (1 + h)`**, whatever the true form: for `v = G u` the bias vanishes and
`|X G⁻ᵀ v|² = uᵀ G u = vᵀ G⁻ v`. -/
theorem meanSquare_error_of_mem_range [IsProbabilityMeasure μ] {e : Ω → Option ι → ℝ} {σ2 : ℝ}
    (hw : White μ e σ2) (X : Matrix ι n ℝ) {Gm : Matrix n n ℝ} (hGm : Xᵀ * X * Gm * (Xᵀ * X) = Xᵀ * X)
    (w u : n → ℝ) :
    ∫ ω, error X Gm w (e ω) ((Xᵀ * X) *ᵥ u) ^ 2 ∂μ =
        σ2 * (1 + ((Xᵀ * X) *ᵥ u) ⬝ᵥ (Gm *ᵥ ((Xᵀ * X) *ᵥ u))) ∧
      ((Xᵀ * X) *ᵥ u) ⬝ᵥ (Gm *ᵥ ((Xᵀ * X) *ᵥ u)) = u ⬝ᵥ ((Xᵀ * X) *ᵥ u) := by
  obtain ⟨hval, hbias, hT⟩ := range_identities (gram_symm X) hGm u w
  have h1 : ∀ b : n → ℝ, (X *ᵥ b) ⬝ᵥ (X *ᵥ b) = ((Xᵀ * X) *ᵥ b) ⬝ᵥ b := fun b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, dotProduct_comm]
  have hnorm : (X *ᵥ (Gmᵀ *ᵥ ((Xᵀ * X) *ᵥ u))) ⬝ᵥ (X *ᵥ (Gmᵀ *ᵥ ((Xᵀ * X) *ᵥ u))) =
      u ⬝ᵥ ((Xᵀ * X) *ᵥ u) := by
    rw [h1, mulVec_mulVec ((Xᵀ * X) *ᵥ u) (Xᵀ * X) Gmᵀ, mulVec_mulVec u (Xᵀ * X * Gmᵀ) (Xᵀ * X), hT,
      dotProduct_mulVec, vecMul_transpose, dotProduct_comm, hval]
  refine ⟨?_, hval⟩
  rw [meanSquare_error hw, hbias, hnorm, hval]
  ring

end Fit

end Holonics.HNN.ReadingLeverageError
