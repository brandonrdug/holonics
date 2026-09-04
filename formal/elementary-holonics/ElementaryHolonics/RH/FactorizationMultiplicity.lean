import ElementaryHolonics.RH.LandauLemma

/-!
# The multiplicity of a zero factorization is the analytic order

A `ZeroFactorization` records a finite comb with multiplicities.  Inside the open half disc,
that multiplicity is the analytic order of `f` at the zero, and the divisor of `f` on any subset
of the half disc is the comb: `mult ρ` at the zeros, `0` elsewhere.  Hence the weighted interior
sum of the rectangle argument principle is the divisor sum, canonical in `f` alone and
independent of the factorization chosen.
-/

open Complex Metric Set Finset Filter Topology
open scoped Classical
open Soma.Holonics.RH.LandauLemma

namespace Soma.Holonics.RH.FactorizationMultiplicity

variable {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization f z₀ r)

/-- The cofactor of `ρ`: the product over the other zeros times the unit. -/
noncomputable def cofactor (ρ : ℂ) (z : ℂ) : ℂ :=
  (∏ σ ∈ Z.zeros.erase ρ, (z - σ) ^ Z.mult σ) * Z.unit z

theorem cofactor_ne_zero {ρ : ℂ} (hρ2 : ρ ∈ ball z₀ (r / 2)) : cofactor Z ρ ρ ≠ 0 :=
  mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun σ hσ =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hσ).symm))
    (Z.unit_ne ρ hρ2)

theorem differentiableOn_cofactor (ρ : ℂ) : DifferentiableOn ℂ (cofactor Z ρ) (ball z₀ r) := by
  unfold cofactor
  have h1 : DifferentiableOn ℂ (fun z => ∏ σ ∈ Z.zeros.erase ρ, (z - σ) ^ Z.mult σ) (ball z₀ r) :=
    DifferentiableOn.fun_finsetProd fun σ _ => by fun_prop
  exact h1.mul Z.unit_diff

theorem factor_cofactor {ρ : ℂ} (hρ : ρ ∈ Z.zeros) {z : ℂ} (hz : z ∈ ball z₀ r) :
    f z = (z - ρ) ^ Z.mult ρ * cofactor Z ρ z := by
  rw [Z.factor z hz, cofactor, ← mul_assoc,
    ← Finset.mul_prod_erase Z.zeros (fun σ => (z - σ) ^ Z.mult σ) hρ]

/-- Inside the open half disc, the multiplicity is the analytic order. -/
theorem analyticOrderAt_eq_mult (hf : DifferentiableOn ℂ f (ball z₀ r)) (hr : 0 < r)
    {ρ : ℂ} (hρ : ρ ∈ Z.zeros) (hρ2 : ρ ∈ ball z₀ (r / 2)) :
    analyticOrderAt f ρ = Z.mult ρ := by
  have hρr : ρ ∈ ball z₀ r := ball_subset_ball (by linarith) hρ2
  have hfa : AnalyticAt ℂ f ρ := (hf.analyticOnNhd isOpen_ball) ρ hρr
  rw [hfa.analyticOrderAt_eq_natCast]
  refine ⟨cofactor Z ρ, ((differentiableOn_cofactor Z ρ).analyticOnNhd isOpen_ball) ρ hρr,
    cofactor_ne_zero Z hρ2, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds hρr] with z hz
  rw [smul_eq_mul]
  exact factor_cofactor Z hρ hz

/-- Inside the open half disc, away from the comb, the analytic order is zero. -/
theorem analyticOrderAt_eq_zero_of_notMem (hf : DifferentiableOn ℂ f (ball z₀ r)) (hr : 0 < r)
    {ρ : ℂ} (hρ : ρ ∉ Z.zeros) (hρ2 : ρ ∈ ball z₀ (r / 2)) :
    analyticOrderAt f ρ = 0 := by
  have hρr : ρ ∈ ball z₀ r := ball_subset_ball (by linarith) hρ2
  have hfa : AnalyticAt ℂ f ρ := (hf.analyticOnNhd isOpen_ball) ρ hρr
  rw [hfa.analyticOrderAt_eq_zero, Z.factor ρ hρr]
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr fun σ hσ =>
      pow_ne_zero _ (sub_ne_zero.mpr fun h => hρ (h ▸ hσ)))
    (Z.unit_ne ρ hρ2)

/-- On any subset of the open half disc, the divisor of `f` is the comb. -/
theorem divisor_eq (hf : DifferentiableOn ℂ f (ball z₀ r)) (hr : 0 < r) {U : Set ℂ}
    (hU : U ⊆ ball z₀ (r / 2)) (u : ℂ) :
    MeromorphicOn.divisor f U u = if u ∈ U then (if u ∈ Z.zeros then (Z.mult u : ℤ) else 0) else 0 := by
  by_cases huU : u ∈ U
  · rw [if_pos huU]
    have hmer : MeromorphicOn f U := fun v hv =>
      ((hf.analyticOnNhd isOpen_ball) v (ball_subset_ball (by linarith) (hU hv))).meromorphicAt
    have hfa : AnalyticAt ℂ f u :=
      (hf.analyticOnNhd isOpen_ball) u (ball_subset_ball (by linarith) (hU huU))
    rw [MeromorphicOn.divisor_apply hmer huU, hfa.meromorphicOrderAt_eq]
    by_cases hz : u ∈ Z.zeros
    · rw [if_pos hz, analyticOrderAt_eq_mult Z hf hr hz (hU huU)]
      simp
    · rw [if_neg hz, analyticOrderAt_eq_zero_of_notMem Z hf hr hz (hU huU)]
      simp
  · rw [if_neg huU]
    exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ huU

/-- The weighted interior comb is the divisor sum. -/
theorem finsum_divisor_eq (hf : DifferentiableOn ℂ f (ball z₀ r)) (hr : 0 < r) {U : Set ℂ}
    (hU : U ⊆ ball z₀ (r / 2)) (h : ℂ → ℂ) :
    ∑ᶠ u, (MeromorphicOn.divisor f U u : ℂ) * h u =
      ∑ ρ ∈ Z.zeros, (if ρ ∈ U then (Z.mult ρ : ℂ) * h ρ else 0) := by
  have hsupp : Function.support (fun u => (MeromorphicOn.divisor f U u : ℂ) * h u) ⊆ ↑Z.zeros := by
    intro u hu
    rw [Function.mem_support] at hu
    by_contra hz
    apply hu
    rw [divisor_eq Z hf hr hU u]
    have hz' : u ∉ Z.zeros := fun h => hz (Finset.mem_coe.mpr h)
    by_cases huU : u ∈ U
    · rw [if_pos huU, if_neg hz']
      simp
    · rw [if_neg huU]
      simp
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [divisor_eq Z hf hr hU ρ]
  by_cases huU : ρ ∈ U
  · rw [if_pos huU, if_pos hρ, if_pos huU]
    push_cast
    ring
  · rw [if_neg huU, if_neg huU]
    simp

end Soma.Holonics.RH.FactorizationMultiplicity
