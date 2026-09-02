import ElementaryHolonics.RH.RectangleCauchy
import ElementaryHolonics.RH.LandauLemma

/-!
# The rectangle argument principle for a zero factorization

Given a `ZeroFactorization` of `f` on a disc (the finite zero comb with multiplicities and a
nonvanishing unit), the weighted rectangle integral of `h · f′/f` around any rectangle inside the
half disc whose boundary meets no zero returns exactly `2 π i · Σ_{ρ inside} m_ρ h(ρ)`.  The log
derivative on the boundary is the Landau flux plus the unit's log derivative; the unit's term is
holomorphic on the rectangle and integrates to zero; each flux term is Cauchy's formula on the
rectangle for interior zeros and Cauchy--Goursat for exterior ones.

This is the zero side of the explicit formula on the contour whose right edge carries the prime
comb.
-/

open Complex Metric Set Finset
open scoped Classical
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.RectangleCauchy

namespace Soma.Holonics.RH.RectangleArgumentPrinciple

variable {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization f z₀ r)

/-- On the half disc, away from the zeros, the log derivative of `f` is the Landau flux plus the
log derivative of the unit. -/
theorem logDeriv_eq_flux_add (hr : 0 < r) {z : ℂ} (hz : z ∈ ball z₀ (r / 2)) (hfz : f z ≠ 0) :
    logDeriv f z = ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ) + logDeriv Z.unit z := by
  have hz' : z ∈ ball z₀ r := ball_subset_ball (by linarith) hz
  have hfeq : f =ᶠ[nhds z] fun w => Z.poly w * Z.unit w := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
    exact Z.factor w hw
  have hpolyz : Z.poly z ≠ 0 := by
    intro h
    have := Z.factor z hz'
    unfold ZeroFactorization.poly at h
    rw [h, zero_mul] at this
    exact hfz this
  have hfactor_ne : ∀ ρ ∈ Z.zeros, z - ρ ≠ 0 := by
    intro ρ hρ h
    apply hpolyz
    unfold ZeroFactorization.poly
    exact Finset.prod_eq_zero hρ (by rw [h, zero_pow (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ hρ))])
  have hpoly_diff : DifferentiableAt ℂ Z.poly z := by
    unfold ZeroFactorization.poly
    exact DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub_const ρ).pow _
  rw [(logDeriv_congr_nhds hfeq).eq_of_nhds,
    logDeriv_mul z hpolyz (Z.unit_ne z hz) hpoly_diff
      (Z.unit_diff.differentiableAt (isOpen_ball.mem_nhds hz'))]
  have hpoly : logDeriv Z.poly z = ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ) := by
    unfold ZeroFactorization.poly
    rw [logDeriv_prod (s := Z.zeros) (f := fun ρ w => (w - ρ) ^ Z.mult ρ) (x := z)
      (fun ρ hρ => pow_ne_zero _ (hfactor_ne ρ hρ))
      (fun ρ _ => (differentiableAt_id.sub_const ρ).pow _)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w => w - ρ) (differentiableAt_id.sub_const ρ), logDeriv_apply,
      deriv_sub_const, deriv_id'']
    ring
  rw [hpoly]

/-- **The rectangle argument principle.**  For a rectangle inside the half disc whose boundary
meets no zero, and a weight `h` holomorphic on the closed rectangle,
`∮ h · f′/f = 2 π i · Σ_{ρ inside} m_ρ · h(ρ)`. -/
theorem rectIntegral_mul_logDeriv (hr : 0 < r) {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hrect : closedRect z w ⊆ ball z₀ (r / 2)) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (closedRect z w))
    (hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w) :
    rectIntegral (fun ζ => h ζ * logDeriv f ζ) z w =
      2 * Real.pi * I *
        ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then (Z.mult ρ : ℂ) * h ρ else 0) := by
  classical
  have hbsub : boundaryRect z w ⊆ ball z₀ (r / 2) :=
    (boundaryRect_subset_closedRect z w).trans hrect
  have hne : ∀ ζ ∈ boundaryRect z w, ∀ ρ ∈ Z.zeros, ζ ≠ ρ :=
    fun ζ hζ ρ hρ e => hbd ρ hρ (e ▸ hζ)
  have hfne : ∀ ζ ∈ boundaryRect z w, f ζ ≠ 0 := by
    intro ζ hζ
    rw [Z.factor ζ (ball_subset_ball (by linarith) (hbsub hζ))]
    exact mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hne ζ hζ ρ hρ)))
      (Z.unit_ne ζ (hbsub hζ))
  have hunit_an : AnalyticOnNhd ℂ Z.unit (ball z₀ r) := Z.unit_diff.analyticOnNhd isOpen_ball
  have hsub : closedRect z w ⊆ ball z₀ r := hrect.trans (ball_subset_ball (by linarith))
  have hlogunit : DifferentiableOn ℂ (fun ζ => h ζ * logDeriv Z.unit ζ) (closedRect z w) := by
    have hd : DifferentiableOn ℂ (deriv Z.unit) (closedRect z w) :=
      hunit_an.deriv.differentiableOn.mono hsub
    have hu : DifferentiableOn ℂ Z.unit (closedRect z w) := Z.unit_diff.mono hsub
    exact hh.mul (hd.div hu fun ζ hζ => Z.unit_ne ζ (hrect hζ))
  have hcongr : rectIntegral (fun ζ => h ζ * logDeriv f ζ) z w =
      rectIntegral (fun ζ => (∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) * (h ζ / (ζ - ρ))) +
        h ζ * logDeriv Z.unit ζ) z w := by
    apply rectIntegral_congr
    intro ζ hζ
    beta_reduce
    rw [logDeriv_eq_flux_add Z hr (hbsub hζ) (hfne ζ hζ), mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  have hE1 : ∀ ρ ∈ Z.zeros,
      ContinuousOn (fun ζ => (Z.mult ρ : ℂ) * (h ζ / (ζ - ρ))) (boundaryRect z w) := by
    intro ρ hρ
    exact continuousOn_const.mul
      ((hh.continuousOn.mono (boundaryRect_subset_closedRect z w)).div
        (continuousOn_id.sub continuousOn_const) fun ζ hζ => sub_ne_zero.mpr (hne ζ hζ ρ hρ))
  rw [hcongr, rectIntegral_add (EdgeIntegrable.of_continuousOn (continuousOn_finsetSum _ hE1))
    (EdgeIntegrable.of_continuousOn
      (hlogunit.continuousOn.mono (boundaryRect_subset_closedRect z w))),
    rectIntegral_eq_zero_of_differentiableOn hlogunit, add_zero,
    rectIntegral_finset_sum _ _ _ _ hE1, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [rectIntegral_const_mul]
  by_cases hin : ρ ∈ openRect z w
  · rw [if_pos hin, rectIntegral_div_sub hzw hin hh.continuousOn
      (hh.mono (openRect_subset_closedRect z w))]
    ring
  · rw [if_neg hin]
    have hout : ρ ∉ closedRect z w := fun hc => hbd ρ hρ ⟨hc, hin⟩
    rw [rectIntegral_div_sub_of_notMem hout hh, mul_zero, mul_zero]

end Soma.Holonics.RH.RectangleArgumentPrinciple
