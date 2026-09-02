import ElementaryHolonics.RH.ZeroFactorizationExists
import ElementaryHolonics.RH.RiemannXiGrowth

/-!
# Landau's lemma for `ξ`

The pointwise abscissa growth `log ‖ξ z‖ ≤ C (‖z‖ + 3) log (‖z‖ + 3)` supplies the growth
budget on every disc: on `ball z₀ r`, `‖ξ z‖ ≤ ‖ξ z₀‖ e^{M}` with
`M = max 1 (C (‖z₀‖ + r + 3) log (‖z₀‖ + r + 3) − log ‖ξ z₀‖)`.  With the constructed zero
factorization, the log-derivative of `ξ` on the `r/8` disc is the Coulomb flux of the zeros of the
half disc plus a background of size `16 (M + N log 2)/r`.  This is the analytic input the
explicit-formula population side needs: the zero comb of `ξ` carries its log-derivative.
-/

noncomputable section

namespace Soma.Holonics.RH.LandauXi

open Complex Metric Set
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.RiemannXiGrowth
open Soma.Holonics.RH.AbscissaGrowth
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists

/-- The growth budget of `ξ` on the disc `ball z₀ r`, with growth constant `C`. -/
def xiBudget (C : ℝ) (z₀ : ℂ) (r : ℝ) : ℝ :=
  max 1 (C * (‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3) - Real.log ‖riemannXi z₀‖)

theorem xiBudget_pos (C : ℝ) (z₀ : ℂ) (r : ℝ) : 0 < xiBudget C z₀ r :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- **The growth bound on a disc.** -/
theorem norm_riemannXi_le_of_growth {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hξ₀ : riemannXi z₀ ≠ 0) {z : ℂ} (hz : z ∈ ball z₀ r) :
    ‖riemannXi z‖ ≤ ‖riemannXi z₀‖ * Real.exp (xiBudget C z₀ r) := by
  have hpos₀ : 0 < ‖riemannXi z₀‖ := norm_pos_iff.mpr hξ₀
  have hnz : ‖z‖ ≤ ‖z₀‖ + r := by
    rw [mem_ball_iff_norm] at hz
    calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + r := by linarith
  have hmono : (‖z‖ + 3) * Real.log (‖z‖ + 3) ≤ (‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3) :=
    mulLog_mono_on_one (by linarith [norm_nonneg z]) (by linarith)
  have hG : Real.log ‖riemannXi z‖ ≤ C * (‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3) := by
    calc Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3) := hgrowth z
      _ = C * ((‖z‖ + 3) * Real.log (‖z‖ + 3)) := by ring
      _ ≤ C * ((‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3)) :=
          mul_le_mul_of_nonneg_left hmono hC.le
      _ = C * (‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3) := by ring
  have hM : C * (‖z₀‖ + r + 3) * Real.log (‖z₀‖ + r + 3) - Real.log ‖riemannXi z₀‖ ≤
      xiBudget C z₀ r := le_max_right _ _
  by_cases hzero : riemannXi z = 0
  · rw [hzero, norm_zero]
    positivity
  · have hpos : 0 < ‖riemannXi z‖ := norm_pos_iff.mpr hzero
    have hlog : Real.log ‖riemannXi z‖ ≤ Real.log ‖riemannXi z₀‖ + xiBudget C z₀ r := by
      linarith
    calc ‖riemannXi z‖ = Real.exp (Real.log ‖riemannXi z‖) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (Real.log ‖riemannXi z₀‖ + xiBudget C z₀ r) := Real.exp_le_exp.mpr hlog
      _ = ‖riemannXi z₀‖ * Real.exp (xiBudget C z₀ r) := by
          rw [Real.exp_add, Real.exp_log hpos₀]

/-- **Landau's lemma for `ξ`.** On every disc about a non-zero of `ξ`, the log-derivative on the
`r/8` disc is the Coulomb flux of the zeros of the half disc plus a background bounded by
`16 (M + N log 2) / r`, where `M` is the growth budget of the pointwise abscissa constant. -/
theorem exists_zeroFactorization_riemannXi {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hξ₀ : riemannXi z₀ ≠ 0) :
    ∃ (C : ℝ) (Z : ZeroFactorization riemannXi z₀ r), 0 < C ∧
      ∀ z ∈ closedBall z₀ (r / 8), riemannXi z ≠ 0 →
        ‖logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤
          16 * (xiBudget C z₀ r + Z.count * Real.log 2) / r := by
  obtain ⟨C, hC, hgrowth⟩ := pointwiseAbscissaGrowthOfRiemannXiHolds
  obtain ⟨Z⟩ := exists_zeroFactorization differentiable_riemannXi hr hξ₀
  refine ⟨C, Z, hC, fun z hz hfz => ?_⟩
  exact Z.norm_logDeriv_sub_flux_le hr (xiBudget_pos C z₀ r) hξ₀
    (fun w hw => norm_riemannXi_le_of_growth hC hgrowth hr hξ₀ hw) hz hfz

end Soma.Holonics.RH.LandauXi
