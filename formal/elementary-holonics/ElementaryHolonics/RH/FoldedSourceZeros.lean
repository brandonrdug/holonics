import ElementaryHolonics.RH.FoldedSourceTail
import ElementaryHolonics.RH.FoldedSourceDerivative

/-!
# Derivative and zero-count receivers of the folded source

Finite folded populations are entire by the actual differentiated event integrals. Their
derivatives converge uniformly on compact sets, and their multiplicity-weighted rectangle counts
eventually agree with the actual standard flow whenever its boundary is zero-free. No assertion
places those zeros on the real axis or computes a zero count without its boundary hypotheses.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedSourceZeros

open Complex Metric Filter Topology Set MeasureTheory
open Soma.Holonics.RH.CriticalChart
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.FoldedSourceTail
open Soma.Holonics.RH.FoldedSourceDerivative
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleWindingContinuity
open Soma.Holonics.RH.RectangleCountStable

theorem hasDerivAt_partialSource (N : ℕ) (t : ℝ) (z : ℂ) :
    HasDerivAt (partialSource N t)
      (∑ n ∈ Finset.range N, ∫ u in Ioi (0 : ℝ), foldedSourceTermDeriv t z n u) z :=
  HasDerivAt.fun_sum (fun n _hn ↦ hasDerivAt_integral_foldedSourceTerm t z n)

theorem differentiable_partialSource (N : ℕ) (t : ℝ) :
    Differentiable ℂ (partialSource N t) := fun z ↦ (hasDerivAt_partialSource N t z).differentiableAt

theorem differentiable_Hstd (t : ℝ) : Differentiable ℂ (Hstd t) := by
  have hc : Differentiable ℂ criticalChart := by unfold criticalChart; fun_prop
  have hheat := Soma.Holonics.RH.XiGrowth.differentiable_heatE_riemannXi (-t / 4)
  have heq : Hstd t = fun z ↦ (1 / 8 : ℂ) * heatE (-t / 4) riemannXi (criticalChart z) :=
    funext (Hstd_eq t)
  rw [heq]
  exact (hheat.comp hc).const_mul _

theorem tendstoUniformlyOn_deriv_partialSource (t : ℝ) {K : Set ℂ} (hK : IsCompact K) :
    TendstoUniformlyOn (fun N ↦ deriv (partialSource N t)) (deriv (Hstd t)) atTop K :=
  (Soma.Holonics.RH.HurwitzLine.tendstoUniformlyOn_deriv
    (Filter.Eventually.of_forall fun N ↦ differentiable_partialSource N t)
    (tendstoLocallyUniformly_partialSource t) hK).2

/-- The whole multiplicity count is retained on every rectangle with an admitted zero-free
boundary. The cutoff is eventual; no numerical cutoff or global RH claim is hidden here. -/
theorem eventually_rectangle_count_eq (t : ℝ) {z w : ℂ}
    (hzw : z.re < w.re ∧ z.im < w.im)
    (hne : ∀ ζ ∈ boundaryRect z w, Hstd t ζ ≠ 0) :
    ∃ k : ℕ,
      (∑ᶠ u, ((MeromorphicOn.divisor (Hstd t) (openRect z w)) u : ℂ)) = k ∧
      ∀ᶠ N : ℕ in atTop,
        (∀ ζ ∈ boundaryRect z w, partialSource N t ζ ≠ 0) ∧
        (∑ᶠ u, ((MeromorphicOn.divisor (partialSource N t) (openRect z w)) u : ℂ)) = k := by
  have hG := differentiable_Hstd t
  have hF : ∀ᶠ N : ℕ in atTop, Differentiable ℂ (partialSource N t) :=
    Filter.Eventually.of_forall fun N ↦ differentiable_partialSource N t
  have hlim := tendstoLocallyUniformly_partialSource t
  obtain ⟨k₀, hw₀, hc₀⟩ := exists_count hG hzw hne
  refine ⟨k₀, hc₀, ?_⟩
  have hK := isCompact_boundaryRect z w
  obtain ⟨hu, _⟩ := Soma.Holonics.RH.HurwitzLine.tendstoUniformlyOn_deriv hF hlim hK
  obtain ⟨m, hm, hbd⟩ := Soma.Holonics.RH.HurwitzLine.eventually_norm_ge
    hu hK hG.continuous.continuousOn hne
  have hwi := Soma.Holonics.RH.HurwitzLine.tendsto_rectIntegral hF hG hlim hne
  have hclose : ∀ᶠ N : ℕ in atTop,
      ‖rectIntegral (logDeriv (partialSource N t)) z w -
        rectIntegral (logDeriv (Hstd t)) z w‖ < 1 := by
    have h := hwi.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h] with N hN
    simpa only [Metric.mem_ball, dist_eq_norm] using hN
  filter_upwards [hbd, hclose] with N hbound hN
  have hneN : ∀ ζ ∈ boundaryRect z w, partialSource N t ζ ≠ 0 :=
    fun ζ hζ ↦ norm_pos_iff.mp (lt_of_lt_of_le hm (hbound ζ hζ))
  obtain ⟨k, hwk, hck⟩ := exists_count (differentiable_partialSource N t) hzw hneN
  have heq : k = k₀ := by
    apply Soma.Holonics.RH.HurwitzPolynomial.nat_eq_of_norm_sub_lt
    rw [hwk, hw₀, ← mul_sub, norm_mul] at hN
    have hfactor : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hfactor] at hN
    nlinarith [mul_nonneg (sub_nonneg.mpr Real.two_le_pi)
      (norm_nonneg ((k : ℂ) - (k₀ : ℂ)))]
  exact ⟨hneN, hck.trans (congrArg (fun n : ℕ ↦ (n : ℂ)) heq)⟩

#print axioms hasDerivAt_partialSource
#print axioms differentiable_Hstd
#print axioms tendstoUniformlyOn_deriv_partialSource
#print axioms eventually_rectangle_count_eq

end Soma.Holonics.RH.FoldedSourceZeros
