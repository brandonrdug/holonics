import Mathlib
import ElementaryHolonics.RH.HeatKernelPhi

/-!
# DB1: the strip of `ξ`

Every zero of `ξ` has `0 < Re s < 1`, from Mathlib's nonvanishing of `ζ` on `Re s ≥ 1`, the
factorization `ξ = ½ s(s−1) Λ(s)`, `ξ(1) = ½`, and the reflection `ξ(1 − s) = ξ(s)`; and no zero
is real, since `ξ(σ) = ∫ e^{(σ−½)u} Φ(u) du > 0` for real `σ`.
-/

noncomputable section

namespace Soma.Holonics.RH.XiStrip

open Complex Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.HeatKernelPhi

/-- `ξ` does not vanish on `Re s ≥ 1`. -/
theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  by_cases h1 : s = 1
  · subst h1
    rw [riemannXi_zero_and_one.2]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [riemannXi_eq_classicalProduct hs0 h1]
  have hζ := riemannZeta_ne_zero_of_one_le_re hs
  have hΛ : completedRiemannZeta s ≠ 0 := by
    have hdef := riemannZeta_def_of_ne_zero hs0
    intro h
    rw [h, zero_div] at hdef
    exact hζ hdef
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs0) h1') hΛ

/-- `ξ` does not vanish on `Re s ≤ 0`. -/
theorem riemannXi_ne_zero_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  apply riemannXi_ne_zero_of_one_le_re
  rw [Complex.sub_re, Complex.one_re]
  linarith

/-- **The strip.** Every zero of `ξ` has `0 < Re s < 1`. -/
theorem re_mem_Ioo_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hc
    push_neg at hc
    exact riemannXi_ne_zero_of_re_nonpos hc h
  · by_contra hc
    push_neg at hc
    exact riemannXi_ne_zero_of_one_le_re hc h

/-- The strip, centred at the seam: `|Re s − ½| < ½`. -/
theorem abs_re_sub_half_lt_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) :
    |s.re - 1 / 2| < 1 / 2 := by
  obtain ⟨h0, h1⟩ := re_mem_Ioo_of_riemannXi_eq_zero h
  rw [abs_lt]
  constructor <;> linarith

/-! ## The real axis -/

/-- On the real axis `ξ` is a positive real: `ξ(σ) = ∫ e^{(σ−½)u} Φ(u) du`. -/
theorem riemannXi_ofReal_pos (σ : ℝ) : ∃ v : ℝ, 0 < v ∧ riemannXi (σ : ℂ) = (v : ℂ) := by
  set g : ℝ → ℝ := fun u => Real.exp ((σ - 1 / 2) * u) * Φ u with hg
  have hgpos : ∀ u, 0 < g u := fun u => mul_pos (Real.exp_pos _) (Φ_pos u)
  have hlap : ∀ u, lap (σ : ℂ) u = ((g u : ℝ) : ℂ) := by
    intro u
    simp only [hg, lap]
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  have hint : Integrable g := by
    have := (integrable_lap (σ : ℂ)).norm
    refine this.congr (Eventually.of_forall fun u => ?_)
    show ‖lap (σ : ℂ) u‖ = g u
    rw [norm_lap]
    simp [hg]
  refine ⟨∫ u : ℝ, g u, ?_, ?_⟩
  · rw [integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun u => (hgpos u).le) hint]
    have hsupp : Function.support g = univ := by
      ext u
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (hgpos u).ne'
    rw [hsupp]
    simp
  · rw [riemannXi_eq_L]
    unfold L
    rw [show (fun u : ℝ => lap (σ : ℂ) u) = fun u => ((g u : ℝ) : ℂ) from funext hlap]
    exact integral_ofReal

theorem riemannXi_ofReal_ne_zero (σ : ℝ) : riemannXi (σ : ℂ) ≠ 0 := by
  obtain ⟨v, hv, h⟩ := riemannXi_ofReal_pos σ
  rw [h]
  exact_mod_cast hv.ne'

/-- **No zero of `ξ` is real.** -/
theorem im_ne_zero_of_riemannXi_eq_zero {s : ℂ} (h : riemannXi s = 0) : s.im ≠ 0 := by
  intro him
  have hs : s = (s.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hs] at h
  exact riemannXi_ofReal_ne_zero s.re h

end Soma.Holonics.RH.XiStrip
