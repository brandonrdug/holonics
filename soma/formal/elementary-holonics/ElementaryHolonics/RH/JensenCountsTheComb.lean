import ElementaryHolonics.RH.LandauXi

/-!
# Jensen counts the comb

The total multiplicity of the constructed zero factorization of `ξ` on the half disc is the
divisor mass of the closed half disc, and Mathlib's Jensen bound controls that mass by the growth
on the three-quarter circle: `N ≤ log (M′/‖ξ z₀‖) / log (3/2)` with `M′ = max 1 (‖ξ z₀‖ e^B)`.
Landau's lemma for `ξ` then carries no free count: on the `r/8` disc,

    ‖ ξ′/ξ − Σ_ρ m_ρ/(z − ρ) ‖ ≤ 16 (B + log 2 · log (M′/‖ξ z₀‖) / log (3/2)) / r.
-/

noncomputable section

namespace Soma.Holonics.RH.JensenCountsTheComb

open Complex Metric Set
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.RiemannXiGrowth
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists
open Soma.Holonics.RH.LandauXi

/-- The Jensen ceiling of the disc: the larger of one and the growth bound on the disc. -/
def jensenCeiling (C : ℝ) (z₀ : ℂ) (r : ℝ) : ℝ :=
  max 1 (‖riemannXi z₀‖ * Real.exp (xiBudget C z₀ r))

theorem one_le_jensenCeiling (C : ℝ) (z₀ : ℂ) (r : ℝ) : 1 ≤ jensenCeiling C z₀ r :=
  le_max_left _ _

/-- **Jensen counts the comb.** The divisor mass of the closed half disc is bounded by the
growth on the three-quarter circle. -/
theorem finsum_divisor_le {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {z₀ : ℂ} {r : ℝ} (hr : 0 < r) (hξ₀ : riemannXi z₀ ≠ 0) :
    ((∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall z₀ (r / 2)) u : ℤ) : ℝ) ≤
      Real.log (jensenCeiling C z₀ r / ‖riemannXi z₀‖) / Real.log (3 / 2) := by
  have hr2 : (0 : ℝ) < |r / 2| := by rw [abs_of_pos (by positivity)]; positivity
  have hlt : |r / 2| < |3 * r / 4| := by
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    linarith
  have han : AnalyticOnNhd ℂ riemannXi (closedBall z₀ |3 * r / 4|) :=
    fun z _ => differentiable_riemannXi.analyticAt z
  have hbound : ∀ z ∈ sphere z₀ |3 * r / 4|, ‖riemannXi z‖ ≤ jensenCeiling C z₀ r := by
    intro z hz
    have hzball : z ∈ ball z₀ r := by
      rw [mem_sphere_iff_norm, abs_of_pos (by positivity)] at hz
      rw [mem_ball_iff_norm, hz]
      linarith
    exact (norm_riemannXi_le_of_growth hC hgrowth hr hξ₀ hzball).trans (le_max_right _ _)
  have h := AnalyticOnNhd.sum_divisor_le hr2 hlt (one_le_jensenCeiling C z₀ r) han hξ₀ hbound
  rw [abs_of_pos (by positivity : (0 : ℝ) < r / 2)] at h
  have hratio : (3 * r / 4) / (r / 2) = 3 / 2 := by
    field_simp
    ring
  rw [hratio] at h
  exact h

/-- **Landau's lemma for `ξ` with Jensen's count.** -/
theorem exists_zeroFactorization_riemannXi_jensen {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hξ₀ : riemannXi z₀ ≠ 0) :
    ∃ (C : ℝ) (Z : ZeroFactorization riemannXi z₀ r), 0 < C ∧
      (Z.count : ℝ) ≤ Real.log (jensenCeiling C z₀ r / ‖riemannXi z₀‖) / Real.log (3 / 2) ∧
      ∀ z ∈ closedBall z₀ (r / 8), riemannXi z ≠ 0 →
        ‖logDeriv riemannXi z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤
          16 * (xiBudget C z₀ r +
            Real.log (jensenCeiling C z₀ r / ‖riemannXi z₀‖) / Real.log (3 / 2) * Real.log 2) /
            r := by
  obtain ⟨C, hC, hgrowth⟩ := pointwiseAbscissaGrowthOfRiemannXiHolds
  obtain ⟨Z, hcount⟩ := exists_zeroFactorization_count differentiable_riemannXi hr hξ₀
  have hN : (Z.count : ℝ) ≤ Real.log (jensenCeiling C z₀ r / ‖riemannXi z₀‖) / Real.log (3 / 2) := by
    have h := finsum_divisor_le hC hgrowth hr hξ₀
    rw [← hcount] at h
    exact_mod_cast h
  refine ⟨C, Z, hC, hN, fun z hz hfz => ?_⟩
  have hL := Z.norm_logDeriv_sub_flux_le hr (xiBudget_pos C z₀ r) hξ₀
    (fun w hw => norm_riemannXi_le_of_growth hC hgrowth hr hξ₀ hw) hz hfz
  refine hL.trans ?_
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_le_mul_of_nonneg_right hN hlog2
  linarith

end Soma.Holonics.RH.JensenCountsTheComb
