import ElementaryHolonics.RH.Xi
import ElementaryHolonics.RH.Jensen
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# The actual entire Riemann xi function

Mathlib's `completedRiemannZeta₀` is the additive pole-removed completion

```text
Λ₀(s) = Λ(s) + 1/s + 1/(1-s).
```

It is entire and reflection invariant, but its zero set is not definitionally the
zero set of `ζ`.  The classical entire Riemann xi function is instead

```text
ξ(s) = 1/2 · s(s-1) Λ(s) = 1/2 · (s(s-1)Λ₀(s) + 1).
```

This file installs that object, proves its entire continuation and reflection law,
and proves that its zeros in the open critical strip are exactly the zeta zeros.
-/

noncomputable section

namespace Soma.Holonics.RH.RiemannXi

open Complex Metric Real MeromorphicOn

/-- The classical entire Riemann xi function, expressed through mathlib's entire
additive completion so no removable singularity remains in the definition. -/
def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The xi function is complex differentiable everywhere. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).mul
    differentiable_completedZeta₀).add_const 1).div_const 2

/-- Xi is analytic on every declared receiver domain. -/
theorem analyticOn_riemannXi (S : Set ℂ) : AnalyticOnNhd ℂ riemannXi S :=
  (analyticOnNhd_univ_iff_differentiable.2 differentiable_riemannXi).mono
    (Set.subset_univ S)

/-- Hence xi has a meromorphic divisor on every receiver domain, with no pole debt. -/
theorem meromorphicOn_riemannXi (S : Set ℂ) : MeromorphicOn riemannXi S :=
  (analyticOn_riemannXi S).meromorphicOn

/-- The xi divisor is nonnegative: it records zeros with multiplicity and no poles. -/
theorem divisor_riemannXi_nonnegative (S : Set ℂ) :
    0 ≤ MeromorphicOn.divisor riemannXi S :=
  (analyticOn_riemannXi S).divisor_nonneg

/-- Jensen's receiver attached to the actual entire xi function. -/
theorem jensen_riemannXi {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (fun z => Real.log ‖riemannXi z‖) c R
      = ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) *
            Real.log (R * ‖c - u‖⁻¹)
        + (MeromorphicOn.divisor riemannXi (closedBall c |R|) c : ℝ) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannXi c‖ :=
  MeromorphicOn.circleAverage_log_norm hR (meromorphicOn_riemannXi _)

/-- Away from the two removed poles, the entire definition is exactly the classical
product `1/2 · s(s-1)Λ(s)`. -/
theorem riemannXi_eq_classicalProduct {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold riemannXi
  have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs1.symm
  field_simp [hs0, h1s]
  ring

/-- The entire xi function carries the same reflection as the completion. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Neither removed endpoint is a zero of xi. -/
theorem riemannXi_zero_and_one : riemannXi 0 = 1 / 2 ∧ riemannXi 1 = 1 / 2 := by
  constructor <;> simp [riemannXi]

/-- In the open critical strip, zeros of the entire xi function are exactly zeros
of the Riemann zeta function. -/
theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs_ne_zero : s ≠ 0 := by
    intro h
    rw [h] at hs0
    norm_num at hs0
  have hs_ne_one : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hs_sub_one : s - 1 ≠ 0 := sub_ne_zero.mpr hs_ne_one
  rw [riemannXi_eq_classicalProduct hs_ne_zero hs_ne_one,
    riemannZeta_def_of_ne_zero hs_ne_zero]
  simp [hs_ne_zero, hs_sub_one, hGamma]

/-- The critical line remains the fixed locus of xi's anti-linear reflection chart. -/
theorem criticalLine_fixedLocus (s : ℂ) :
    1 - (starRingEnd ℂ) s = s ↔ s.re = 1 / 2 :=
  Soma.Holonics.RH.theCriticalLineIsTheFixedLocus s

end Soma.Holonics.RH.RiemannXi
