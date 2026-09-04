import Mathlib
import ElementaryHolonics.RH.HurwitzLine
import ElementaryHolonics.RH.HeatKernelPhi
import ElementaryHolonics.RH.HeatFlowContinuity
import ElementaryHolonics.RH.XiGrowth
import ElementaryHolonics.RH.TrivialZeros
import ElementaryHolonics.RH.ConjugationEntire

/-!
# FT4 (iv): the seam times are closed, and the threshold

In the standard coordinate `τ = −t`, `H_τ = heatE (−τ) ξ`. The *seam times* are the `τ` at which
every zero of `H_τ` lies on the seam `Re z = ½`. `0` is a seam time iff the Riemann Hypothesis
(`TrivialZeros.riemannHypothesis_iff_xi`). The flow is jointly continuous, so it converges locally
uniformly along every convergent sequence of times, and Hurwitz (`HurwitzLine.zeros_on_seam`) makes
the seam times closed. `Λ_DN` is their infimum; given that they are a nonempty up-set (forward
preservation, FT4 (iii)), `RH ⟺ Λ_DN ≤ 0`. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.RealZeroTimes

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatFlowContinuity
open Soma.Holonics.RH.ConjugationEntire
open Soma.Holonics.RH.TrivialZeros
open Soma.Holonics.RH.HeatKernelPhi

/-- **The seam times**, in the standard coordinate `τ = −t`: every zero of `H_τ = heatE (−τ) ξ`
lies on the seam. -/
def seamTimes : Set ℝ := {τ | ∀ z, heatE (-τ) riemannXi z = 0 → z.re = 1 / 2}

/-- **`0` is a seam time iff the Riemann Hypothesis.** -/
theorem zero_mem_iff : (0 : ℝ) ∈ seamTimes ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_xi]
  simp only [seamTimes, mem_setOf_eq, neg_zero, heatE_zero]

/-- The flow converges locally uniformly along every convergent sequence of times. -/
theorem tendstoLocallyUniformly_heatE {τ : ℝ} {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 τ)) :
    TendstoLocallyUniformly (fun n => heatE (t n) riemannXi) (heatE τ riemannXi) atTop := by
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  have hc := continuous_heatE differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num)
    (by norm_num) (by norm_num)
  have hca := hc.continuousAt (x := (τ, x))
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨δ, hδ, hδ'⟩ := hca (ε / 2) (by positivity)
  refine ⟨ball x δ, ball_mem_nhds x hδ, ?_⟩
  have hev : ∀ᶠ n in atTop, dist (t n) τ < δ := (Metric.tendsto_nhds.mp ht) δ hδ
  filter_upwards [hev] with n hn y hy
  rw [mem_ball] at hy
  have h1 := hδ' (x := (t n, y)) (by rw [Prod.dist_eq]; exact max_lt hn hy)
  have h2 := hδ' (x := (τ, y)) (by rw [Prod.dist_eq]; exact max_lt (by simpa using hδ) hy)
  simp only at h1 h2
  calc dist (heatE τ riemannXi y) (heatE (t n) riemannXi y)
      ≤ dist (heatE τ riemannXi y) (heatE τ riemannXi x) +
          dist (heatE τ riemannXi x) (heatE (t n) riemannXi y) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h2 (by rw [dist_comm]; exact h1)
    _ = ε := by ring

/-- **The seam times are closed.** -/
theorem isClosed_seamTimes : IsClosed seamTimes := by
  rw [← isSeqClosed_iff_isClosed]
  intro τn τ hτn hlim z hz
  exact HurwitzLine.zeros_on_seam (Eventually.of_forall fun n => differentiable_heatE_riemannXi _)
    (differentiable_heatE_riemannXi _) (tendstoLocallyUniformly_heatE hlim.neg)
    ⟨1 / 2, heatE_riemannXi_half_ne_zero _⟩ (Eventually.of_forall hτn) z hz

/-- **The de Bruijn–Newman threshold** in the standard coordinate: the infimum of the seam
times. -/
def Λ_DN : ℝ := sInf seamTimes

/-- **`RH ⟺ Λ_DN ≤ 0`**, given that the seam times are a nonempty up-set. -/
theorem riemannHypothesis_iff_Λ_DN_le (hne : seamTimes.Nonempty)
    (hup : ∀ τ ∈ seamTimes, ∀ τ', τ ≤ τ' → τ' ∈ seamTimes) : RiemannHypothesis ↔ Λ_DN ≤ 0 := by
  rw [← zero_mem_iff]
  constructor
  · intro h0
    by_cases hbdd : BddBelow seamTimes
    · exact csInf_le hbdd h0
    · unfold Λ_DN
      rw [Real.sInf_of_not_bddBelow hbdd]
  · intro hΛ
    by_cases hbdd : BddBelow seamTimes
    · have hmem : Λ_DN ∈ seamTimes := isClosed_seamTimes.csInf_mem hne hbdd
      exact hup _ hmem 0 hΛ
    · rw [not_bddBelow_iff] at hbdd
      obtain ⟨τ, hτ, hτ0⟩ := hbdd 0
      exact hup τ hτ 0 hτ0.le

end Soma.Holonics.RH.RealZeroTimes
