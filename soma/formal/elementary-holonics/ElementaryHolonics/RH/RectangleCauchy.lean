import Mathlib

/-!
# The rectangle as a receiver: Cauchy's formula on a rectangle

Mathlib carries the Cauchy--Goursat theorem on a rectangle (the boundary integral of a
holomorphic function is zero) but not the residue form.  The explicit formula for the zeros of
`ξ` needs the rectangle: the prime comb converges only to the right of the line `Re s = 1`, so a
circle through the critical strip cannot carry the prime side, while a rectangle with its right
edge at `Re s > 1` can.  This owner returns the rectangle residue of `1 / (ζ - ρ)` exactly as
`2 π i` when `ρ` lies inside, through the four logarithmic primitives along the edges, and from
it the Cauchy formula `∮ g(ζ) / (ζ - ρ) = 2 π i g(ρ)`.

Everything here is elementary: the only ingredients are Mathlib's rectangle Cauchy--Goursat
theorem, the derivative of the principal logarithm off the slit, and the two argument identities
`arg (-x) = arg x ± π` on the two half-planes.
-/

open Complex Set MeasureTheory intervalIntegral Metric Filter Topology
open scoped Interval

namespace ElementaryHolonics.RH.RectangleCauchy

/-- The positively oriented boundary integral of `f` around the rectangle with corners `z` and
`w`, in the exact shape of Mathlib's `integral_boundary_rect_*` conclusions. -/
noncomputable def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- The closed rectangle. -/
def closedRect (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

/-- The open rectangle. -/
def openRect (z w : ℂ) : Set ℂ :=
  Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)

/-- The boundary of the rectangle. -/
def boundaryRect (z w : ℂ) : Set ℂ := closedRect z w \ openRect z w

theorem isOpen_openRect (z w : ℂ) : IsOpen (openRect z w) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

theorem openRect_subset_closedRect (z w : ℂ) : openRect z w ⊆ closedRect z w := by
  intro ζ hζ
  rw [openRect, Complex.mem_reProdIm] at hζ
  rw [closedRect, Complex.mem_reProdIm]
  exact ⟨Ioo_subset_Icc_self hζ.1, Ioo_subset_Icc_self hζ.2⟩

theorem boundaryRect_subset_closedRect (z w : ℂ) : boundaryRect z w ⊆ closedRect z w :=
  sdiff_subset

theorem openRect_bounds {z w ρ : ℂ} (hzw : z.re < w.re ∧ z.im < w.im) (hρ : ρ ∈ openRect z w) :
    (z.re < ρ.re ∧ ρ.re < w.re) ∧ (z.im < ρ.im ∧ ρ.im < w.im) := by
  rw [openRect, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo, min_eq_left hzw.1.le,
    max_eq_right hzw.1.le, min_eq_left hzw.2.le, max_eq_right hzw.2.le] at hρ
  exact hρ

theorem mem_openRect_of_bounds {z w ρ : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (h : (z.re < ρ.re ∧ ρ.re < w.re) ∧ (z.im < ρ.im ∧ ρ.im < w.im)) : ρ ∈ openRect z w := by
  rw [openRect, Complex.mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo, min_eq_left hzw.1.le,
    max_eq_right hzw.1.le, min_eq_left hzw.2.le, max_eq_right hzw.2.le]
  exact h

/-! ### The four edges lie on the boundary -/

theorem re_horizontal (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
theorem im_horizontal (x y : ℝ) : ((x : ℂ) + (y : ℂ) * I).im = y := by simp

theorem not_mem_Ioo_left (a b : ℝ) : a ∉ Ioo (min a b) (max a b) := by
  simp only [Set.mem_Ioo, min_lt_iff, lt_max_iff, lt_self_iff_false, false_or, not_and]
  intro h1 h2
  exact lt_asymm h1 h2

theorem not_mem_Ioo_right (a b : ℝ) : b ∉ Ioo (min a b) (max a b) := by
  simp only [Set.mem_Ioo, min_lt_iff, lt_max_iff, lt_self_iff_false, or_false, not_and]
  intro h1 h2
  exact lt_asymm h1 h2

theorem bottom_mem {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + z.im * I ∈ boundaryRect z w := by
  refine ⟨?_, ?_⟩
  · rw [closedRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact ⟨hx, left_mem_uIcc⟩
  · rw [openRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact fun h => not_mem_Ioo_left z.im w.im h.2

theorem top_mem {z w : ℂ} {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + w.im * I ∈ boundaryRect z w := by
  refine ⟨?_, ?_⟩
  · rw [closedRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact ⟨hx, right_mem_uIcc⟩
  · rw [openRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact fun h => not_mem_Ioo_right z.im w.im h.2

theorem right_mem {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (w.re : ℂ) + y * I ∈ boundaryRect z w := by
  refine ⟨?_, ?_⟩
  · rw [closedRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact ⟨right_mem_uIcc, hy⟩
  · rw [openRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact fun h => not_mem_Ioo_right z.re w.re h.1

theorem left_mem {z w : ℂ} {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (z.re : ℂ) + y * I ∈ boundaryRect z w := by
  refine ⟨?_, ?_⟩
  · rw [closedRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact ⟨left_mem_uIcc, hy⟩
  · rw [openRect, Complex.mem_reProdIm, re_horizontal, im_horizontal]
    exact fun h => not_mem_Ioo_left z.re w.re h.1

/-! ### Edge integrability and the algebra of the rectangle integral -/

/-- Integrability of `f` along the four edges. -/
def EdgeIntegrable (f : ℂ → ℂ) (z w : ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f (x + z.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun x : ℝ => f (x + w.im * I)) volume z.re w.re ∧
  IntervalIntegrable (fun y : ℝ => f (w.re + y * I)) volume z.im w.im ∧
  IntervalIntegrable (fun y : ℝ => f (z.re + y * I)) volume z.im w.im

theorem EdgeIntegrable.of_continuousOn {f : ℂ → ℂ} {z w : ℂ}
    (h : ContinuousOn f (boundaryRect z w)) : EdgeIntegrable f z w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (h.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + z.im * I).continuousOn
      (fun x hx => bottom_mem hx)).intervalIntegrable
  · exact (h.comp (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + w.im * I).continuousOn
      (fun x hx => top_mem hx)).intervalIntegrable
  · exact (h.comp (by fun_prop : Continuous fun y : ℝ => (w.re : ℂ) + y * I).continuousOn
      (fun y hy => right_mem hy)).intervalIntegrable
  · exact (h.comp (by fun_prop : Continuous fun y : ℝ => (z.re : ℂ) + y * I).continuousOn
      (fun y hy => left_mem hy)).intervalIntegrable

theorem rectIntegral_add {f g : ℂ → ℂ} {z w : ℂ} (hf : EdgeIntegrable f z w)
    (hg : EdgeIntegrable g z w) :
    rectIntegral (fun ζ => f ζ + g ζ) z w = rectIntegral f z w + rectIntegral g z w := by
  simp only [rectIntegral]
  rw [intervalIntegral.integral_add hf.1 hg.1, intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  simp only [smul_add]
  ring

theorem rectIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectIntegral (fun ζ => c * f ζ) z w = c * rectIntegral f z w := by
  simp only [rectIntegral, intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem rectIntegral_congr {f g : ℂ → ℂ} {z w : ℂ} (h : EqOn f g (boundaryRect z w)) :
    rectIntegral f z w = rectIntegral g z w := by
  have hb : EqOn (fun x : ℝ => f (x + z.im * I)) (fun x : ℝ => g (x + z.im * I))
      (uIcc z.re w.re) := fun x hx => h (bottom_mem hx)
  have ht : EqOn (fun x : ℝ => f (x + w.im * I)) (fun x : ℝ => g (x + w.im * I))
      (uIcc z.re w.re) := fun x hx => h (top_mem hx)
  have hr : EqOn (fun y : ℝ => f (w.re + y * I)) (fun y : ℝ => g (w.re + y * I))
      (uIcc z.im w.im) := fun y hy => h (right_mem hy)
  have hl : EqOn (fun y : ℝ => f (z.re + y * I)) (fun y : ℝ => g (z.re + y * I))
      (uIcc z.im w.im) := fun y hy => h (left_mem hy)
  simp only [rectIntegral]
  rw [intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ht,
    intervalIntegral.integral_congr hr, intervalIntegral.integral_congr hl]

theorem rectIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (z w : ℂ)
    (hf : ∀ i ∈ s, ContinuousOn (f i) (boundaryRect z w)) :
    rectIntegral (fun ζ => ∑ i ∈ s, f i ζ) z w = ∑ i ∈ s, rectIntegral (f i) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectIntegral]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hsplit : (fun ζ => ∑ i ∈ insert a s, f i ζ) = fun ζ => f a ζ + ∑ i ∈ s, f i ζ := by
      funext ζ
      rw [Finset.sum_insert ha]
    rw [hsplit, rectIntegral_add (EdgeIntegrable.of_continuousOn (hf a (Finset.mem_insert_self a s)))
      (EdgeIntegrable.of_continuousOn
        (continuousOn_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- Cauchy--Goursat on the rectangle, in the `rectIntegral` shape. -/
theorem rectIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ} {z w : ℂ}
    (H : DifferentiableOn ℂ f (closedRect z w)) : rectIntegral f z w = 0 :=
  integral_boundary_rect_eq_zero_of_differentiableOn f z w H

theorem rectIntegral_div_sub_of_notMem {g : ℂ → ℂ} {z w ρ : ℂ} (hρ : ρ ∉ closedRect z w)
    (hg : DifferentiableOn ℂ g (closedRect z w)) :
    rectIntegral (fun ζ => g ζ / (ζ - ρ)) z w = 0 :=
  rectIntegral_eq_zero_of_differentiableOn
    (hg.div (differentiableOn_id.sub (differentiableOn_const ρ)) fun ζ hζ =>
      sub_ne_zero.mpr (ne_of_mem_of_not_mem hζ hρ))

/-! ### The logarithmic primitives along the four edges -/

theorem integral_inv_horizontal {ρ : ℂ} {x₁ x₂ y : ℝ} (hy : y ≠ ρ.im) :
    ∫ x in x₁..x₂, ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹ =
      log ((x₂ : ℂ) + y * I - ρ) - log ((x₁ : ℂ) + y * I - ρ) := by
  have him : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I - ρ).im = y - ρ.im := by intro x; simp
  have hne : ∀ x : ℝ, (x : ℂ) + (y : ℂ) * I - ρ ≠ 0 := by
    intro x h
    have := congrArg Complex.im h
    rw [him] at this
    simp only [zero_im] at this
    exact hy (sub_eq_zero.mp this)
  have hslit : ∀ x : ℝ, (x : ℂ) + (y : ℂ) * I - ρ ∈ slitPlane := by
    intro x
    rw [mem_slitPlane_iff, him]
    exact Or.inr (sub_ne_zero.mpr hy)
  have hderiv : ∀ x ∈ uIcc x₁ x₂, HasDerivAt (fun t : ℝ => log ((t : ℂ) + (y : ℂ) * I - ρ))
      ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹ x := by
    intro x _
    have h1 : HasDerivAt (fun ζ : ℂ => ζ + (y : ℂ) * I - ρ) 1 (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)).sub_const ρ
    have h2 := (Complex.hasStrictDerivAt_log (hslit x)).hasDerivAt.comp (x : ℂ) h1
    have h3 := h2.comp_ofReal
    simpa [Function.comp] using h3
  have hint : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹) volume x₁ x₂ := by
    apply Continuous.intervalIntegrable
    exact ((continuous_ofReal.add continuous_const).sub continuous_const).inv₀ hne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem integral_inv_vertical_right {ρ : ℂ} {x y₁ y₂ : ℝ} (hx : ρ.re < x) :
    I • ∫ y in y₁..y₂, ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹ =
      log ((x : ℂ) + y₂ * I - ρ) - log ((x : ℂ) + y₁ * I - ρ) := by
  rw [← intervalIntegral.integral_smul]
  have hre : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I - ρ).re = x - ρ.re := by intro y; simp
  have hne : ∀ y : ℝ, (x : ℂ) + (y : ℂ) * I - ρ ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    rw [hre] at this
    simp only [zero_re] at this
    linarith
  have hslit : ∀ y : ℝ, (x : ℂ) + (y : ℂ) * I - ρ ∈ slitPlane := by
    intro y
    rw [mem_slitPlane_iff, hre]
    exact Or.inl (by linarith)
  have hderiv : ∀ y ∈ uIcc y₁ y₂, HasDerivAt (fun t : ℝ => log ((x : ℂ) + (t : ℂ) * I - ρ))
      (I • ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun ζ : ℂ => (x : ℂ) + ζ * I - ρ) I (y : ℂ) := by
      simpa using (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const ρ
    have h2 := (Complex.hasStrictDerivAt_log (hslit y)).hasDerivAt.comp (y : ℂ) h1
    have h3 := h2.comp_ofReal
    simp only [Function.comp, smul_eq_mul] at h3 ⊢
    exact h3.congr_deriv (mul_comm _ _)
  have hint : IntervalIntegrable (fun y : ℝ => I • ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹) volume y₁ y₂ := by
    apply Continuous.intervalIntegrable
    exact (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const).inv₀ hne).const_smul I
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem integral_inv_vertical_left {ρ : ℂ} {x y₁ y₂ : ℝ} (hx : x < ρ.re) :
    I • ∫ y in y₁..y₂, ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹ =
      log (-((x : ℂ) + y₂ * I - ρ)) - log (-((x : ℂ) + y₁ * I - ρ)) := by
  rw [← intervalIntegral.integral_smul]
  have hre : ∀ y : ℝ, (-((x : ℂ) + (y : ℂ) * I - ρ)).re = ρ.re - x := by intro y; simp
  have hne : ∀ y : ℝ, (x : ℂ) + (y : ℂ) * I - ρ ≠ 0 := by
    intro y h
    have := congrArg Complex.re (congrArg Neg.neg h)
    rw [hre] at this
    simp only [neg_zero, zero_re] at this
    linarith
  have hslit : ∀ y : ℝ, -((x : ℂ) + (y : ℂ) * I - ρ) ∈ slitPlane := by
    intro y
    rw [mem_slitPlane_iff, hre]
    exact Or.inl (by linarith)
  have hderiv : ∀ y ∈ uIcc y₁ y₂, HasDerivAt (fun t : ℝ => log (-((x : ℂ) + (t : ℂ) * I - ρ)))
      (I • ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹) y := by
    intro y _
    have h0 : HasDerivAt (fun ζ : ℂ => (x : ℂ) + ζ * I - ρ) I (y : ℂ) := by
      simpa using (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const ρ
    have h1 : HasDerivAt (fun ζ : ℂ => -((x : ℂ) + ζ * I - ρ)) (-I) (y : ℂ) := h0.neg
    have h2 := (Complex.hasStrictDerivAt_log (hslit y)).hasDerivAt.comp (y : ℂ) h1
    have h3 := h2.comp_ofReal
    simp only [Function.comp, smul_eq_mul] at h3 ⊢
    exact h3.congr_deriv (by rw [inv_neg, neg_mul_neg, mul_comm])
  have hint : IntervalIntegrable (fun y : ℝ => I • ((x : ℂ) + (y : ℂ) * I - ρ)⁻¹) volume y₁ y₂ := by
    apply Continuous.intervalIntegrable
    exact (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
      continuous_const).inv₀ hne).const_smul I
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem log_neg_of_im_neg {x : ℂ} (h : x.im < 0) : log (-x) = log x + Real.pi * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_add_pi_of_im_neg h]

theorem log_neg_of_im_pos {x : ℂ} (h : 0 < x.im) : log (-x) = log x - Real.pi * I := by
  apply Complex.ext
  · simp [log_re]
  · simp [log_im, arg_neg_eq_arg_sub_pi_of_im_pos h]

/-! ### The residue of `1 / (ζ - ρ)` on the rectangle -/

/-- The rectangle winds once around every interior point: the four logarithmic primitives
cancel in modulus and return `2 π` in argument. -/
theorem rectIntegral_inv_sub {z w ρ : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hρ : ρ ∈ openRect z w) : rectIntegral (fun ζ => (ζ - ρ)⁻¹) z w = 2 * Real.pi * I := by
  obtain ⟨hre, him⟩ := openRect_bounds hzw hρ
  simp only [rectIntegral]
  rw [integral_inv_horizontal (ne_of_lt him.1), integral_inv_horizontal (ne_of_gt him.2),
    integral_inv_vertical_right hre.2, integral_inv_vertical_left hre.1]
  have h11 : ((z.re : ℂ) + (z.im : ℂ) * I - ρ).im = z.im - ρ.im := by simp
  have h12 : ((z.re : ℂ) + (w.im : ℂ) * I - ρ).im = w.im - ρ.im := by simp
  have e1 := log_neg_of_im_neg (x := (z.re : ℂ) + (z.im : ℂ) * I - ρ) (by rw [h11]; linarith)
  have e2 := log_neg_of_im_pos (x := (z.re : ℂ) + (w.im : ℂ) * I - ρ) (by rw [h12]; linarith)
  rw [e1, e2]
  ring

/-- **Cauchy's integral formula on a rectangle.** -/
theorem rectIntegral_div_sub {g : ℂ → ℂ} {z w ρ : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hρ : ρ ∈ openRect z w) (hc : ContinuousOn g (closedRect z w))
    (hd : DifferentiableOn ℂ g (openRect z w)) :
    rectIntegral (fun ζ => g ζ / (ζ - ρ)) z w = 2 * Real.pi * I * g ρ := by
  have hopen := isOpen_openRect z w
  have hρd : DifferentiableAt ℂ g ρ := hd.differentiableAt (hopen.mem_nhds hρ)
  have hnhds : closedRect z w ∈ 𝓝 ρ :=
    Filter.mem_of_superset (hopen.mem_nhds hρ) (openRect_subset_closedRect z w)
  have hcd : ContinuousOn (dslope g ρ) (closedRect z w) := (continuousOn_dslope hnhds).2 ⟨hc, hρd⟩
  have h0 : rectIntegral (dslope g ρ) z w = 0 := by
    apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope g ρ) z w {ρ}
      (countable_singleton ρ) hcd
    intro x hx
    have hne : x ≠ ρ := fun h => hx.2 (by rw [h]; exact Set.mem_singleton ρ)
    rw [differentiableAt_dslope_of_ne hne]
    exact hd.differentiableAt (hopen.mem_nhds hx.1)
  have hbne : ∀ ζ ∈ boundaryRect z w, ζ ≠ ρ := fun ζ hζ h => hζ.2 (h ▸ hρ)
  have hcongr : rectIntegral (fun ζ => g ζ / (ζ - ρ)) z w =
      rectIntegral (fun ζ => dslope g ρ ζ + g ρ * (ζ - ρ)⁻¹) z w := by
    apply rectIntegral_congr
    intro ζ hζ
    have hne := hbne ζ hζ
    show g ζ / (ζ - ρ) = dslope g ρ ζ + g ρ * (ζ - ρ)⁻¹
    rw [dslope_of_ne g hne, slope_def_field, ← div_eq_mul_inv, ← add_div, sub_add_cancel]
  have hE1 : EdgeIntegrable (dslope g ρ) z w :=
    EdgeIntegrable.of_continuousOn (hcd.mono (boundaryRect_subset_closedRect z w))
  have hE2 : EdgeIntegrable (fun ζ => g ρ * (ζ - ρ)⁻¹) z w :=
    EdgeIntegrable.of_continuousOn (continuousOn_const.mul
      ((continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => sub_ne_zero.mpr (hbne ζ hζ)))
  rw [hcongr, rectIntegral_add hE1 hE2, h0, rectIntegral_const_mul, rectIntegral_inv_sub hzw hρ,
    zero_add]
  ring

end ElementaryHolonics.RH.RectangleCauchy
