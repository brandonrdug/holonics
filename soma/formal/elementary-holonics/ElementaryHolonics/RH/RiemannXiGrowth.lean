import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.AbscissaGrowth

/-!
# Order-one growth and Jensen counting for the classical Riemann xi function

`RH.AbscissaGrowth` proves an unconditional pointwise envelope for mathlib's additive
pole-removed completion `completedRiemannZeta₀`.  The Riemann hypothesis is instead naturally
attached to the classical entire function

```text
riemannXi(s) = (s(s-1) completedRiemannZeta₀(s) + 1) / 2.
```

This file pays for that polynomial-and-constant passage explicitly.  It then applies Jensen's
formula to `riemannXi` itself, so the returned divisor is the divisor of the classical xi function
and not a substituted zero population from the additive completion.

Every theorem below is `[proved-derived]`.  The resulting estimate controls the total weighted
zero population in a disc; `[open]` it does not place those zeros on the critical line and therefore
does not prove RH.
-/

noncomputable section

namespace Soma.Holonics.RH.RiemannXiGrowth

open Complex Metric Set Real MeromorphicOn
open Soma.Holonics.RH.AbscissaGrowth
open Soma.Holonics.RH.RiemannXi

/-- The pointwise order-one receiver, now attached to the classical entire xi function. -/
def PointwiseAbscissaGrowthOfRiemannXi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
    Real.log ‖riemannXi z‖
      ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3)

/-- The translated-circle receiver needed by Jensen, now attached to `riemannXi`. -/
def AbscissaGrowthOfRiemannXi : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (c : ℂ) (R : ℝ), 1 ≤ R →
    circleAverage (fun z => Real.log ‖riemannXi z‖) c R
      ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)

/-- `[proved-derived]` The additive completion's pointwise envelope survives multiplication by
`s(s-1)`, addition of one, and division by two.  Three copies of the common shifted radial
envelope pay respectively for the two polynomial factors and the additive triangle term. -/
theorem pointwiseRiemannXiGrowth_of_completedGrowth
    (hP : PointwiseAbscissaGrowthOfXi) : PointwiseAbscissaGrowthOfRiemannXi := by
  obtain ⟨C, hC, hcompleted⟩ := hP
  refine ⟨C + 3, by linarith, fun z => ?_⟩
  let F : ℝ := (‖z‖ + 3) * Real.log (‖z‖ + 3)
  let a : ℂ := z * (z - 1) * completedRiemannZeta₀ z
  have hlogT : 1 ≤ Real.log (‖z‖ + 3) := by
    exact (Real.le_log_iff_exp_le (by positivity : 0 < ‖z‖ + 3)).2
      (Real.exp_one_lt_three.le.trans (by nlinarith [norm_nonneg z]))
  have hF_reach : ‖z‖ + 3 ≤ F := by
    dsimp [F]
    nlinarith [norm_nonneg z]
  have hF_one : 1 ≤ F := by
    linarith [norm_nonneg z]
  have hF_nonneg : 0 ≤ F := le_trans (by norm_num) hF_one
  have htarget_nonneg : 0 ≤ (C + 3) * F :=
    mul_nonneg (by linarith) hF_nonneg
  have hxi_norm : ‖riemannXi z‖ ≤ ‖a‖ + 1 := by
    calc
      ‖riemannXi z‖ = ‖a + 1‖ / 2 := by
        simp [riemannXi, a]
      _ ≤ (‖a‖ + 1) / 2 := by
        gcongr
        simpa using norm_add_le a (1 : ℂ)
      _ ≤ ‖a‖ + 1 := by nlinarith [norm_nonneg a]
  by_cases hxi : riemannXi z = 0
  · rw [hxi, norm_zero, Real.log_zero]
    simpa [F, mul_assoc] using htarget_nonneg
  have hxi_pos : 0 < ‖riemannXi z‖ := norm_pos_iff.mpr hxi
  by_cases ha : a = 0
  · have hnorm_le_one : ‖riemannXi z‖ ≤ 1 := by
      simpa [ha] using hxi_norm
    have hlog_nonpos : Real.log ‖riemannXi z‖ ≤ 0 :=
      (Real.log_nonpos_iff hxi_pos.le).2 hnorm_le_one
    exact hlog_nonpos.trans (by simpa [F, mul_assoc] using htarget_nonneg)
  have ha_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hz : z ≠ 0 := by
    intro hz
    apply ha
    simp [a, hz]
  have hz1 : z - 1 ≠ 0 := by
    intro hz1
    apply ha
    simp [a, hz1]
  have hcompleted_ne : completedRiemannZeta₀ z ≠ 0 := by
    intro hzero
    apply ha
    simp [a, hzero]
  have hlog_z : Real.log ‖z‖ ≤ F := by
    have h := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)
    linarith
  have hlog_z1 : Real.log ‖z - 1‖ ≤ F := by
    have hnorm : ‖z - 1‖ ≤ ‖z‖ + 1 := by
      calc
        ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = ‖z‖ + 1 := by simp
    have h := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz1)
    linarith
  have hlog_completed : Real.log ‖completedRiemannZeta₀ z‖ ≤ C * F := by
    simpa [F, mul_assoc] using hcompleted z
  have hlog_a : Real.log ‖a‖
      = Real.log ‖z‖ + Real.log ‖z - 1‖
          + Real.log ‖completedRiemannZeta₀ z‖ := by
    dsimp [a]
    rw [norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hz)
        (norm_ne_zero_iff.mpr hz1)) (norm_ne_zero_iff.mpr hcompleted_ne),
      Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hz1)]
  have hlog_a_bound : Real.log ‖a‖ ≤ (C + 2) * F := by
    rw [hlog_a]
    nlinarith
  have hlog_two : Real.log 2 ≤ F := by
    have hlog_two_le_one : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at this ⊢
      exact this
    exact hlog_two_le_one.trans hF_one
  rcases le_total ‖a‖ 1 with ha_small | ha_large
  · have hnorm_le_two : ‖riemannXi z‖ ≤ 2 := hxi_norm.trans (by linarith)
    have hlog_le_two : Real.log ‖riemannXi z‖ ≤ Real.log 2 :=
      Real.log_le_log hxi_pos hnorm_le_two
    calc
      Real.log ‖riemannXi z‖ ≤ Real.log 2 := hlog_le_two
      _ ≤ F := hlog_two
      _ ≤ (C + 3) * F := by nlinarith [hC, hF_nonneg]
      _ = (C + 3) * (‖z‖ + 3) * Real.log (‖z‖ + 3) := by
        simp [F, mul_assoc]
  · have hnorm_le : ‖riemannXi z‖ ≤ 2 * ‖a‖ :=
      hxi_norm.trans (by linarith)
    have hlog_le : Real.log ‖riemannXi z‖ ≤ Real.log (2 * ‖a‖) :=
      Real.log_le_log hxi_pos hnorm_le
    calc
      Real.log ‖riemannXi z‖ ≤ Real.log (2 * ‖a‖) := hlog_le
      _ = Real.log 2 + Real.log ‖a‖ := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha_pos.ne']
      _ ≤ F + (C + 2) * F := add_le_add hlog_two hlog_a_bound
      _ = (C + 3) * F := by ring
      _ = (C + 3) * (‖z‖ + 3) * Real.log (‖z‖ + 3) := by
        simp [F, mul_assoc]

/-- `[proved-derived]` A pointwise xi envelope descends to the translated-circle receiver. -/
theorem pointwiseGrowth_gives_abscissaGrowth
    (hP : PointwiseAbscissaGrowthOfRiemannXi) : AbscissaGrowthOfRiemannXi := by
  obtain ⟨C, hC, hpoint⟩ := hP
  refine ⟨4 * C, mul_pos (by norm_num) hC, fun c R hR => ?_⟩
  apply circleAverage_mono_on_of_le_circle
  · exact circleIntegrable_log_norm_meromorphicOn
      (meromorphicOn_riemannXi (sphere c |R|))
  intro z hz
  have hR0 : 0 ≤ R := by linarith
  have hnorm : ‖z‖ + 3 ≤ (‖c‖ + R + 2) + 1 := by
    linarith [norm_le_center_add_radius hR0 hz]
  have hmono₁ : (‖z‖ + 3) * Real.log (‖z‖ + 3)
      ≤ ((‖c‖ + R + 2) + 1) * Real.log ((‖c‖ + R + 2) + 1) :=
    mulLog_mono_on_one (by nlinarith [norm_nonneg z]) hnorm
  have hmono₂ : ((‖c‖ + R + 2) + 1) * Real.log ((‖c‖ + R + 2) + 1)
      ≤ 4 * ((‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)) :=
    addOne_mulLog_le_four (by nlinarith [norm_nonneg c])
  exact (hpoint z).trans (by
    have := mul_le_mul_of_nonneg_left (hmono₁.trans hmono₂) hC.le
    nlinarith)

/-- `[proved-derived]` Jensen's clean nonzero-centre identity for the divisor of the classical
xi function. -/
theorem weightedRiemannXiZeros_eq_boundaryAverage {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    (hc : riemannXi c ≠ 0) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)
      = circleAverage (fun z => Real.log ‖riemannXi z‖) c R
          - Real.log ‖riemannXi c‖ := by
  have hmem : c ∈ closedBall c |R| := Metric.mem_closedBall_self (abs_nonneg R)
  have hord : MeromorphicOn.divisor riemannXi (closedBall c |R|) c = 0 := by
    have hA : AnalyticAt ℂ riemannXi c :=
      analyticOn_riemannXi Set.univ c (Set.mem_univ c)
    have hz : analyticOrderAt riemannXi c = 0 := hA.analyticOrderAt_eq_zero.2 hc
    have hm : meromorphicOrderAt riemannXi c = 0 := by
      rw [hA.meromorphicOrderAt_eq, hz]
      rfl
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem, hm]
    rfl
  have htc : meromorphicTrailingCoeffAt riemannXi c = riemannXi c :=
    (analyticOn_riemannXi Set.univ c (Set.mem_univ c)).meromorphicTrailingCoeffAt_of_ne_zero hc
  rw [jensen_riemannXi hR, hord, htc]
  push_cast
  ring

/-- `[proved-derived]` Any translated-circle xi envelope bounds its own weighted zero divisor. -/
theorem weightedRiemannXiCount_of_abscissaGrowth
    (hG : AbscissaGrowthOfRiemannXi) {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : riemannXi c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)
            - Real.log ‖riemannXi c‖ := by
  obtain ⟨C, hC, hbound⟩ := hG
  refine ⟨C, hC, ?_⟩
  rw [weightedRiemannXiZeros_eq_boundaryAverage (by linarith) hc]
  linarith [hbound c R hR]

/-- `[proved-derived]` The classical xi pointwise growth receiver is unconditional. -/
theorem pointwiseAbscissaGrowthOfRiemannXiHolds : PointwiseAbscissaGrowthOfRiemannXi :=
  pointwiseRiemannXiGrowth_of_completedGrowth thePointwiseAbscissaGrowthHolds

/-- `[proved-derived]` The classical xi translated-circle growth receiver is unconditional. -/
theorem abscissaGrowthOfRiemannXiHolds : AbscissaGrowthOfRiemannXi :=
  pointwiseGrowth_gives_abscissaGrowth pointwiseAbscissaGrowthOfRiemannXiHolds

/-- `[proved-derived]` Every translated disc of radius at least one, centred away from a xi zero,
has an unconditional weighted multiplicity bound for the classical xi divisor. -/
theorem weightedRiemannXiCount_isUnconditionallyBounded {c : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hc : riemannXi c ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) *
          Real.log (R * ‖c - u‖⁻¹)
        ≤ C * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2)
            - Real.log ‖riemannXi c‖ :=
  weightedRiemannXiCount_of_abscissaGrowth abscissaGrowthOfRiemannXiHolds hR hc

end Soma.Holonics.RH.RiemannXiGrowth
