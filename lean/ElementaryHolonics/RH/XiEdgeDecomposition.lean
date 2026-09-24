import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.RectangleCauchy
import ElementaryHolonics.RH.PrimeSideVertical

/-!
# The edges of the ξ rectangle

Right of the line `Re s = 1`, the entire `ξ` is the classical product
`½ · s (s − 1) · Γ_ℝ(s) · ζ(s)`, so its log derivative is an archimedean part
`1/s + 1/(s − 1) + Γ_ℝ′/Γ_ℝ` plus `ζ′/ζ`, and `−ζ′/ζ` is the prime comb.  The reflection
`ξ(1 − s) = ξ(s)` gives `ξ′/ξ(1 − s) = −ξ′/ξ(s)`, which folds the left edge of a rectangle
symmetric about the critical line onto its right edge with the reflected weight `h(1 − s)`.

This owner returns those identities and the right edge as the prime comb minus the archimedean
integral, in the exact shape the rectangle argument principle consumes.
-/

open Complex Metric Set MeasureTheory intervalIntegral Filter Topology
open scoped Interval
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.PrimeSideVertical

namespace Soma.Holonics.RH.XiEdgeDecomposition

theorem differentiableAt_Gammaℝ_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h : DifferentiableAt ℂ (fun s => ((Gammaℝ s)⁻¹)⁻¹) s :=
    (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  simpa only [inv_inv] using h

theorem ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 0 := by
  intro h
  rw [h] at hs
  norm_num at hs

theorem ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h] at hs
  norm_num at hs

/-- Right of the line `Re s = 1`, `ξ` is the classical product with `ζ`. -/
theorem riemannXi_eq_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  rw [riemannXi_eq_classicalProduct (ne_zero_of_one_lt_re hs) (ne_one_of_one_lt_re hs),
    riemannZeta_def_of_ne_zero (ne_zero_of_one_lt_re hs)]
  field_simp

/-- The archimedean part of `ξ′/ξ`. -/
noncomputable def archimedean (s : ℂ) : ℂ := 1 / s + 1 / (s - 1) + logDeriv Gammaℝ s

theorem isOpen_re_gt (c : ℝ) : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const continuous_re

/-- Right of the line `Re s = 1`, `ξ′/ξ` is the archimedean part plus `ζ′/ζ`. -/
theorem logDeriv_riemannXi_eq {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannXi s = archimedean s + logDeriv riemannZeta s := by
  have hs0 := ne_zero_of_one_lt_re hs
  have hs1 := ne_one_of_one_lt_re hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hfeq : riemannXi =ᶠ[nhds s]
      fun s => ((1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) * riemannZeta s := by
    filter_upwards [(isOpen_re_gt 1).mem_nhds hs] with t ht
    exact riemannXi_eq_mul_zeta ht
  rw [(logDeriv_congr_nhds hfeq).eq_of_nhds]
  have hA : DifferentiableAt ℂ (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) s := by fun_prop
  have hGd := differentiableAt_Gammaℝ_of_re_pos (by linarith : 0 < s.re)
  have hζd := differentiableAt_riemannZeta hs1
  have hAne : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
  rw [logDeriv_mul (f := fun s => (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s) (g := riemannZeta) s
    (mul_ne_zero hAne hG) hζ (hA.mul hGd) hζd,
    logDeriv_mul (f := fun s => (1 / 2 : ℂ) * s * (s - 1)) (g := Gammaℝ) s hAne hG hA hGd]
  have hpoly : logDeriv (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) s = 1 / s + 1 / (s - 1) := by
    rw [logDeriv_apply]
    have hd : HasDerivAt (fun s : ℂ => (1 / 2 : ℂ) * s * (s - 1)) _ s :=
      ((hasDerivAt_id s).const_mul (1 / 2 : ℂ)).mul ((hasDerivAt_id s).sub_const 1)
    rw [hd.deriv]
    simp only [id_eq, mul_one]
    field_simp
  rw [hpoly, archimedean]

/-! ### The reflection -/

theorem hasDerivAt_riemannXi_one_sub (s : ℂ) :
    HasDerivAt riemannXi (-deriv riemannXi (1 - s)) s := by
  have h1 : HasDerivAt (fun s : ℂ => 1 - s) (-1) s := (hasDerivAt_id s).const_sub 1
  have h2 := (differentiable_riemannXi (1 - s)).hasDerivAt.comp s h1
  have hfun : (riemannXi ∘ fun s : ℂ => 1 - s) = riemannXi := by
    funext t
    simp [Function.comp, riemannXi_one_sub]
  rw [hfun] at h2
  exact h2.congr_deriv (by ring)

theorem deriv_riemannXi_one_sub (s : ℂ) : deriv riemannXi (1 - s) = -deriv riemannXi s := by
  rw [(hasDerivAt_riemannXi_one_sub s).deriv]
  ring

/-- `ξ′/ξ (1 − s) = −ξ′/ξ (s)`, at every `s`. -/
theorem logDeriv_riemannXi_one_sub (s : ℂ) :
    logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_riemannXi_one_sub, riemannXi_one_sub, neg_div]

/-- On a rectangle symmetric about the critical line and about the real axis, the left edge
of `h · ξ′/ξ` is the right edge with the reflected weight `h(1 − s)`, up to sign. -/
theorem left_edge_eq {h : ℂ → ℂ} {z w : ℂ} (hsym : z.re + w.re = 1) (hT : z.im = -w.im) :
    I • ∫ y in z.im..w.im, h (z.re + y * I) * logDeriv riemannXi (z.re + y * I) =
      -(I • ∫ y in z.im..w.im,
        h (1 - (w.re + y * I)) * logDeriv riemannXi (w.re + y * I)) := by
  have key : ∀ y : ℝ, h (z.re + y * I) * logDeriv riemannXi (z.re + y * I) =
      -(h (1 - (w.re + ((-y : ℝ) : ℂ) * I)) * logDeriv riemannXi (w.re + ((-y : ℝ) : ℂ) * I)) := by
    intro y
    have hz : (z.re : ℂ) = 1 - w.re := by
      have : z.re = 1 - w.re := by linarith
      rw [this]
      push_cast
      ring
    have e : (z.re : ℂ) + y * I = 1 - ((w.re : ℂ) + ((-y : ℝ) : ℂ) * I) := by
      rw [hz]
      push_cast
      ring
    rw [e, logDeriv_riemannXi_one_sub, mul_neg]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, smul_neg]
  congr 2
  rw [intervalIntegral.integral_comp_neg
    (fun y : ℝ => h (1 - (w.re + y * I)) * logDeriv riemannXi (w.re + y * I)), hT, neg_neg]

/-- The rectangle integral of `h · ξ′/ξ` with both vertical edges folded onto the right edge. -/
theorem rectIntegral_riemannXi_fold {h : ℂ → ℂ} {z w : ℂ} (hsym : z.re + w.re = 1)
    (hT : z.im = -w.im) :
    rectIntegral (fun ζ => h ζ * logDeriv riemannXi ζ) z w =
      (∫ x : ℝ in z.re..w.re, h (x + z.im * I) * logDeriv riemannXi (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, h (x + w.im * I) * logDeriv riemannXi (x + w.im * I)) +
      I • (∫ y in z.im..w.im, h (w.re + y * I) * logDeriv riemannXi (w.re + y * I)) +
      I • (∫ y in z.im..w.im, h (1 - (w.re + y * I)) * logDeriv riemannXi (w.re + y * I)) := by
  simp only [rectIntegral]
  rw [left_edge_eq hsym hT, sub_neg_eq_add]

/-! ### The right edge is the prime comb minus the archimedean integral -/

theorem continuousOn_logDeriv_riemannXi :
    ContinuousOn (logDeriv riemannXi) {s : ℂ | 1 < s.re} := by
  have hd : Continuous (deriv riemannXi) :=
    continuousOn_univ.mp (analyticOn_riemannXi univ).deriv.continuousOn
  have hne : ∀ s ∈ {s : ℂ | 1 < s.re}, riemannXi s ≠ 0 := by
    intro s hs
    rw [riemannXi_eq_mul_zeta hs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_zero_of_one_lt_re hs))
      (sub_ne_zero.mpr (ne_one_of_one_lt_re hs))) (Gammaℝ_ne_zero_of_re_pos (by
        show 0 < s.re
        exact lt_trans zero_lt_one hs))) (riemannZeta_ne_zero_of_one_lt_re hs)
  show ContinuousOn (fun s => deriv riemannXi s / riemannXi s) _
  exact hd.continuousOn.div differentiable_riemannXi.continuous.continuousOn hne

theorem continuousOn_archimedean : ContinuousOn archimedean {s : ℂ | 1 < s.re} := by
  have hsub : {s : ℂ | 1 < s.re} ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    linarith
  have hGd : DifferentiableOn ℂ Gammaℝ {s : ℂ | 0 < s.re} :=
    fun s hs => (differentiableAt_Gammaℝ_of_re_pos hs).differentiableWithinAt
  have hG := (hGd.analyticOnNhd (isOpen_re_gt 0)).deriv.continuousOn.mono hsub
  have hlog : ContinuousOn (logDeriv Gammaℝ) {s : ℂ | 1 < s.re} := by
    show ContinuousOn (fun s => deriv Gammaℝ s / Gammaℝ s) _
    exact hG.div (hGd.continuousOn.mono hsub) fun s hs => Gammaℝ_ne_zero_of_re_pos (hsub hs)
  unfold archimedean
  refine ContinuousOn.add (ContinuousOn.add ?_ ?_) hlog
  · exact continuousOn_const.div continuousOn_id fun s hs => ne_zero_of_one_lt_re hs
  · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      fun s hs => sub_ne_zero.mpr (ne_one_of_one_lt_re hs)

theorem edge_mem {σ : ℝ} (hσ : 1 < σ) (t : ℝ) : edge σ t ∈ {s : ℂ | 1 < s.re} := by
  show 1 < (edge σ t).re
  rw [re_edge]
  exact hσ

/-- **The right edge.**  For a continuous weight `g` and `σ > 1`, the prime comb sums to the
archimedean integral minus the edge integral of `g · ξ′/ξ`. -/
theorem hasSum_right_edge {g : ℂ → ℂ} (hg : Continuous g) {σ : ℝ} (hσ : 1 < σ) (a b : ℝ) :
    HasSum (fun n => ∫ t in a..b, g (edge σ t) * LSeries.term vonMangoldtC (edge σ t) n)
      ((∫ t in a..b, g (edge σ t) * archimedean (edge σ t)) -
        ∫ t in a..b, g (edge σ t) * logDeriv riemannXi (edge σ t)) := by
  have h0 := hasSum_integral_term hg hσ a b
  have hA : IntervalIntegrable (fun t => g (edge σ t) * archimedean (edge σ t)) volume a b :=
    ((hg.comp (continuous_edge σ)).continuousOn.mul
      (continuousOn_archimedean.comp (continuous_edge σ).continuousOn
        fun t _ => edge_mem hσ t)).intervalIntegrable
  have hX : IntervalIntegrable (fun t => g (edge σ t) * logDeriv riemannXi (edge σ t)) volume a b :=
    ((hg.comp (continuous_edge σ)).continuousOn.mul
      (continuousOn_logDeriv_riemannXi.comp (continuous_edge σ).continuousOn
        fun t _ => edge_mem hσ t)).intervalIntegrable
  have heq : (∫ t in a..b, g (edge σ t) * archimedean (edge σ t)) -
      (∫ t in a..b, g (edge σ t) * logDeriv riemannXi (edge σ t)) =
      ∫ t in a..b, g (edge σ t) * (-(deriv riemannZeta (edge σ t) / riemannZeta (edge σ t))) := by
    rw [← intervalIntegral.integral_sub hA hX]
    apply intervalIntegral.integral_congr
    intro t _
    simp only
    rw [logDeriv_riemannXi_eq (edge_mem hσ t), logDeriv_apply]
    ring
  rw [heq]
  exact h0

end Soma.Holonics.RH.XiEdgeDecomposition
