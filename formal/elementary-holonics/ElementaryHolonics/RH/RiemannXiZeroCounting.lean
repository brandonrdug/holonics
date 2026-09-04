import ElementaryHolonics.RH.RiemannXiGrowth
import ElementaryHolonics.RH.ZeroCounting

/-!
# Unconditional inner-disc zero count for the classical Riemann xi function

`RiemannXiGrowth` returns an unconditional Jensen-weighted divisor bound for `riemannXi`.
This file performs the radius-doubling passage: every xi zero in the inner disc pays at least
`log 2` to the outer Jensen receiver, while every zero in the annulus pays a nonnegative weight.

The result is `[proved-derived]` and retains multiplicity through the divisor.  `[open]` It bounds
how many zeros occur in a disc; it does not constrain their horizontal placement and hence does
not prove RH.
-/

noncomputable section

namespace Soma.Holonics.RH.RiemannXiZeroCounting

open Complex Metric Set Real MeromorphicOn
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.RiemannXiGrowth

/-- The classical-xi multiplicity population in the inner disc, read inside the doubled domain. -/
def innerRiemannXiZeroCount (c : ℂ) (R : ℝ) : ℝ :=
  by
    classical
    exact ∑ᶠ u, if u ∈ closedBall c R then
      (MeromorphicOn.divisor riemannXi (closedBall c |2 * R|) u : ℝ)
    else 0

/-- `[proved-derived]` Restricting the doubled divisor to the inner disc retains exactly the inner
divisor mass. -/
theorem innerRiemannXiZeroCount_eq_divisorMass {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    innerRiemannXiZeroCount c R =
      ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c R) u : ℝ) := by
  classical
  unfold innerRiemannXiZeroCount
  apply finsum_congr
  intro u
  by_cases hu : u ∈ closedBall c R
  · rw [if_pos hu]
    have hout : u ∈ closedBall c |2 * R| := by
      have hdist := Metric.mem_closedBall.mp hu
      apply Metric.mem_closedBall.mpr
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
      linarith
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hout,
      MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu]
  · rw [if_neg hu]
    simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, hu]

/-- `[proved-derived]` The inner classical-xi divisor mass is nonnegative because xi is entire. -/
theorem innerRiemannXiZeroCount_nonnegative {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ innerRiemannXiZeroCount c R := by
  rw [innerRiemannXiZeroCount_eq_divisorMass hR]
  exact finsum_nonneg fun u => by
    exact_mod_cast (divisor_riemannXi_nonnegative (closedBall c R)) u

/-- Every point in the support of the doubled classical-xi divisor has a nonnegative outer
Jensen weight when the centre is not itself a zero. -/
theorem outerRiemannXiWeight_nonnegative {c u : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : riemannXi c ≠ 0)
    (hu : MeromorphicOn.divisor riemannXi (closedBall c |2 * R|) u ≠ 0) :
    0 ≤ Real.log ((2 * R) * ‖c - u‖⁻¹) := by
  let D := MeromorphicOn.divisor riemannXi (closedBall c |2 * R|)
  have hmem : u ∈ closedBall c |2 * R| := D.supportWithinDomain hu
  have hDc : D c = 0 := by
    have hmemc : c ∈ closedBall c |2 * R| :=
      Metric.mem_closedBall_self (abs_nonneg _)
    have hA : AnalyticAt ℂ riemannXi c :=
      analyticOn_riemannXi Set.univ c (Set.mem_univ c)
    have hz : analyticOrderAt riemannXi c = 0 := hA.analyticOrderAt_eq_zero.2 hc
    have hm : meromorphicOrderAt riemannXi c = 0 := by
      rw [hA.meromorphicOrderAt_eq, hz]
      rfl
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmemc, hm]
    rfl
  have huc : u ≠ c := by
    intro h
    exact hu (by simpa [D, h] using hDc)
  have hnormpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
  have habs : |2 * R| = 2 * R := abs_of_pos (mul_pos (by norm_num) hR)
  have hnorm : ‖c - u‖ ≤ 2 * R := by
    rw [← Complex.dist_eq]
    have := Metric.mem_closedBall.mp hmem
    simpa [dist_comm, habs] using this
  apply Real.log_nonneg
  rw [le_mul_inv_iff₀ hnormpos]
  simpa using hnorm

/-- `[proved-derived]` The radius-`R` xi multiplicity population is paid for by the radius-`2R`
Jensen population. -/
theorem logTwo_mul_innerRiemannXiZeroCount_le_weightedOuterCount
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hc : riemannXi c ≠ 0) :
    Real.log 2 * innerRiemannXiZeroCount c R ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannXi
          (closedBall c |2 * R|) u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) := by
  classical
  let D := MeromorphicOn.divisor riemannXi (closedBall c |2 * R|)
  have hfinite : D.support.Finite := D.finiteSupport (isCompact_closedBall c |2 * R|)
  have hDnonneg : 0 ≤ D := divisor_riemannXi_nonnegative _
  have hpoint : ∀ u : ℂ,
      Real.log 2 * (if u ∈ closedBall c R then (D u : ℝ) else 0)
        ≤ (D u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) := by
    intro u
    rcases eq_or_ne (D u) 0 with hDu | hDu
    · simp [hDu]
    have hDcast : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hDnonneg u
    by_cases huinner : u ∈ closedBall c R
    · have huc : u ≠ c := by
        intro h
        subst u
        have hmemc : c ∈ closedBall c |2 * R| :=
          Metric.mem_closedBall_self (abs_nonneg _)
        have hA : AnalyticAt ℂ riemannXi c :=
          analyticOn_riemannXi Set.univ c (Set.mem_univ c)
        have hz : analyticOrderAt riemannXi c = 0 := hA.analyticOrderAt_eq_zero.2 hc
        have hm : meromorphicOrderAt riemannXi c = 0 := by
          rw [hA.meromorphicOrderAt_eq, hz]
          rfl
        have hzero : D c = 0 := by
          rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmemc, hm]
          rfl
        exact hDu hzero
      rw [if_pos huinner]
      have hw := Soma.Holonics.RH.ZeroCounting.log_two_le_outerWeight huinner huc
      nlinarith
    · rw [if_neg huinner, mul_zero]
      exact mul_nonneg hDcast (outerRiemannXiWeight_nonnegative hR hc hDu)
  have hleftSupport : ∀ u : ℂ,
      (if u ∈ closedBall c R then (D u : ℝ) else 0) ≠ 0 → u ∈ hfinite.toFinset := by
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      simp [hzero] at hu
    exact hfinite.mem_toFinset.mpr hDu
  have hrightSupport : ∀ u : ℂ,
      (D u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) ≠ 0 →
        u ∈ hfinite.toFinset := by
    intro u hu
    have hDu : D u ≠ 0 := by
      intro hzero
      simp [hzero] at hu
    exact hfinite.mem_toFinset.mpr hDu
  rw [innerRiemannXiZeroCount]
  rw [mul_finsum]
  calc
    ∑ᶠ u, Real.log 2 * (if u ∈ closedBall c R then (D u : ℝ) else 0)
        = ∑ u ∈ hfinite.toFinset,
            Real.log 2 * (if u ∈ closedBall c R then (D u : ℝ) else 0) := by
              apply finsum_eq_sum_of_support_subset
              intro u hu
              apply hleftSupport u
              intro hz
              apply hu
              change Real.log 2 *
                (if u ∈ closedBall c R then (D u : ℝ) else 0) = 0
              rw [hz, mul_zero]
    _ ≤ ∑ u ∈ hfinite.toFinset,
          (D u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) := by
            exact Finset.sum_le_sum fun u _ => hpoint u
    _ = ∑ᶠ u, (D u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) := by
          symm
          apply finsum_eq_sum_of_support_subset
          exact hrightSupport

/-- `[proved-derived]` The unconditional order-one xi growth estimate gives a genuine inner-disc
multiplicity bound for the classical xi divisor. -/
theorem innerRiemannXiZeroCount_isUnconditionallyBounded {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : riemannXi c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      Real.log 2 * innerRiemannXiZeroCount c R ≤
        C * (‖c‖ + 2 * R + 2) * Real.log (‖c‖ + 2 * R + 2)
          - Real.log ‖riemannXi c‖ := by
  obtain ⟨C, hC, hbound⟩ := weightedRiemannXiCount_isUnconditionallyBounded
    (c := c) (R := 2 * R) (by linarith) hc
  refine ⟨C, hC, (logTwo_mul_innerRiemannXiZeroCount_le_weightedOuterCount
    (c := c) (R := R) (by linarith) hc).trans ?_⟩
  simpa [abs_of_nonneg (by positivity : 0 ≤ 2 * R)] using hbound

end Soma.Holonics.RH.RiemannXiZeroCounting
