import ElementaryHolonics.RH.AbscissaGrowth

/-!
# From the Jensen receiver to an honest inner zero count

`RH.AbscissaGrowth` bounds the logarithmically weighted divisor of the completed zeta function in
an outer disc.  A zero in the concentric half-radius disc pays at least `log 2` to that receiver.
This file makes that elementary but essential passage exact: the weighted Jensen population really
controls the multiplicity count on the smaller disc.

No location statement follows.  In particular, this is a zero-density/growth entrance, not the
Riemann hypothesis and not Weil positivity.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroCounting

open Complex Metric Set Real MeromorphicOn
open Soma.Holonics.RH.Jensen Soma.Holonics.RH.AbscissaGrowth

/-- The multiplicity population in the inner disc, read from the divisor on the doubled disc.
The doubled domain keeps the lineage to the Jensen receiver explicit. -/
def innerZeroCount (c : ℂ) (R : ℝ) : ℝ :=
  by
    classical
    exact ∑ᶠ u, if u ∈ closedBall c R then
      (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |2 * R|) u : ℝ)
    else 0

/-- The receiver definition is exactly the total divisor mass on the inner disc: changing from the
doubled ambient divisor to the inner restriction loses no multiplicity. -/
theorem innerZeroCount_eq_divisorMass {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    innerZeroCount c R =
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c R) u : ℝ) := by
  classical
  unfold innerZeroCount
  apply finsum_congr
  intro u
  by_cases hu : u ∈ closedBall c R
  · rw [if_pos hu]
    have hout : u ∈ closedBall c |2 * R| := by
      have hdist := Metric.mem_closedBall.mp hu
      apply Metric.mem_closedBall.mpr
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * R)]
      linarith
    rw [MeromorphicOn.divisor_apply (theXiIsMeromorphicOn _) hout,
      MeromorphicOn.divisor_apply (theXiIsMeromorphicOn _) hu]
  · rw [if_neg hu]
    simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, hu]

/-- The inner multiplicity population is nonnegative because the completed zeta function is
entire and therefore has no pole debt. -/
theorem innerZeroCount_nonnegative {c : ℂ} {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ innerZeroCount c R := by
  rw [innerZeroCount_eq_divisorMass hR]
  exact finsum_nonneg fun u => by
    exact_mod_cast (theXiDivisorIsNonnegative (closedBall c R)) u

/-- A point in the radius-`R` disc, other than its centre, contributes at least `log 2` to the
radius-`2R` Jensen weight. -/
theorem log_two_le_outerWeight {c u : ℂ} {R : ℝ}
    (hu : u ∈ closedBall c R) (huc : u ≠ c) :
    Real.log 2 ≤ Real.log ((2 * R) * ‖c - u‖⁻¹) := by
  have hnorm : ‖c - u‖ ≤ R := by
    rw [← Complex.dist_eq]
    simpa [dist_comm] using Metric.mem_closedBall.mp hu
  have hnormpos : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr huc.symm)
  have hratio : (2 : ℝ) ≤ (2 * R) * ‖c - u‖⁻¹ := by
    rw [le_mul_inv_iff₀ hnormpos]
    nlinarith
  exact Real.log_le_log (by norm_num) hratio

/-- Every point in the support of the doubled-disc divisor has a nonnegative Jensen weight. -/
theorem outerWeight_nonnegative {c u : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : completedRiemannZeta₀ c ≠ 0)
    (hu : MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |2 * R|) u ≠ 0) :
    0 ≤ Real.log ((2 * R) * ‖c - u‖⁻¹) := by
  let D := MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |2 * R|)
  have hmem : u ∈ closedBall c |2 * R| := D.supportWithinDomain hu
  have hDc : D c = 0 := by
    have hmemc : c ∈ closedBall c |2 * R| := Metric.mem_closedBall_self (abs_nonneg _)
    have hA : AnalyticAt ℂ completedRiemannZeta₀ c :=
      theXiIsAnalyticOn Set.univ c (Set.mem_univ c)
    have hz : analyticOrderAt completedRiemannZeta₀ c = 0 :=
      hA.analyticOrderAt_eq_zero.2 hc
    have hm : meromorphicOrderAt completedRiemannZeta₀ c = 0 := by
      rw [hA.meromorphicOrderAt_eq, hz]
      rfl
    rw [MeromorphicOn.divisor_apply (theXiIsMeromorphicOn _) hmemc, hm]
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

/-- **THE HALF-RADIUS COUNT IS PAID FOR BY THE OUTER JENSEN POPULATION.**  Each inner zero pays
at least `log 2`; zeros in the annulus pay a nonnegative amount.  Multiplicity is retained through
the divisor rather than replaced by a set cardinality. -/
theorem logTwo_mul_innerZeroCount_le_weightedOuterCount {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hc : completedRiemannZeta₀ c ≠ 0) :
    Real.log 2 * innerZeroCount c R ≤
      ∑ᶠ u, (MeromorphicOn.divisor completedRiemannZeta₀
          (closedBall c |2 * R|) u : ℝ) * Real.log ((2 * R) * ‖c - u‖⁻¹) := by
  classical
  let D := MeromorphicOn.divisor completedRiemannZeta₀ (closedBall c |2 * R|)
  have hfinite : D.support.Finite := D.finiteSupport (isCompact_closedBall c |2 * R|)
  have hDnonneg : 0 ≤ D := theXiDivisorIsNonnegative _
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
        have hmemc : c ∈ closedBall c |2 * R| := Metric.mem_closedBall_self (abs_nonneg _)
        have hA : AnalyticAt ℂ completedRiemannZeta₀ c :=
          theXiIsAnalyticOn Set.univ c (Set.mem_univ c)
        have hz : analyticOrderAt completedRiemannZeta₀ c = 0 :=
          hA.analyticOrderAt_eq_zero.2 hc
        have hm : meromorphicOrderAt completedRiemannZeta₀ c = 0 := by
          rw [hA.meromorphicOrderAt_eq, hz]
          rfl
        have hzero : D c = 0 := by
          rw [MeromorphicOn.divisor_apply (theXiIsMeromorphicOn _) hmemc, hm]
          rfl
        exact hDu hzero
      rw [if_pos huinner]
      have hw := log_two_le_outerWeight huinner huc
      nlinarith
    · rw [if_neg huinner, mul_zero]
      exact mul_nonneg hDcast (outerWeight_nonnegative hR hc hDu)
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
  rw [innerZeroCount]
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

/-- **THE UNCONDITIONAL INNER ZERO-COUNT BOUND.**  The order-one growth theorem on the outer
disc and the `log 2` payment above combine into a genuine multiplicity-count estimate on the inner
disc.  This is the standard radius-doubling passage, now attached to the actual completed-zeta
divisor. -/
theorem theInnerZeroCountIsUnconditionallyBounded {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : completedRiemannZeta₀ c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      Real.log 2 * innerZeroCount c R ≤
        C * (‖c‖ + 2 * R + 2) * Real.log (‖c‖ + 2 * R + 2)
          - Real.log ‖completedRiemannZeta₀ c‖ := by
  obtain ⟨C, hC, hbound⟩ := theCorrectedWeightedZeroCount
    (c := c) (R := 2 * R) (by linarith) hc
  refine ⟨C, hC, (logTwo_mul_innerZeroCount_le_weightedOuterCount
    (c := c) (R := R) (by linarith) hc).trans ?_⟩
  simpa [abs_of_nonneg (by positivity : 0 ≤ 2 * R)] using hbound

end Soma.Holonics.RH.ZeroCounting
