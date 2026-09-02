import ElementaryHolonics.Millennium.BirchSwinnertonDyerWinding

/-!
# The centre is isolated: a small rectangle returns the analytic rank

A nonzero entire function has isolated zeros, so about the centre `1` there is a radius on
whose closed ball `L` vanishes at most at `1`.  The square of half that radius about `1` is a
rectangle to which the winding theorem applies: `∮ L′/L = 2πi · analyticRank` around it, with no
isolation hypothesis left.
-/

open Complex Metric Set Filter Topology
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.BirchSwinnertonDyerFiniteRank
open Soma.Holonics.Millennium.BirchSwinnertonDyerWinding
open Soma.Holonics.RH.RectangleCauchy

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerWindingIsolated

variable {n : ℕ}

/-- A nonzero entire function has isolated zeros. -/
theorem exists_isolated {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hne : ∃ s, f s ≠ 0) (a : ℂ) :
    ∃ ε > 0, ∀ ζ ∈ closedBall a ε, f ζ = 0 → ζ = a := by
  have han : AnalyticAt ℂ f a := hf.analyticAt a
  rcases han.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hU : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
    have hzero := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ a) h
    obtain ⟨s, hs⟩ := hne
    exact hs (hzero (mem_univ s))
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
    refine ⟨ε / 2, by positivity, fun ζ hζ hf0 => ?_⟩
    by_contra hne'
    have hd : dist ζ a < ε := by
      rw [mem_closedBall] at hζ
      linarith
    exact hball hd hne' hf0

theorem re_corner (δ : ℝ) : (1 - (δ : ℂ) * (1 + I)).re = 1 - δ := by simp
theorem im_corner (δ : ℝ) : (1 - (δ : ℂ) * (1 + I)).im = -δ := by simp
theorem re_corner' (δ : ℝ) : (1 + (δ : ℂ) * (1 + I)).re = 1 + δ := by simp
theorem im_corner' (δ : ℝ) : (1 + (δ : ℂ) * (1 + I)).im = δ := by simp

/-- **A small square about the centre returns the analytic rank.** -/
theorem exists_square_winding (W : LDatum n) {m : ℕ} (hm : analyticRank W = m) :
    ∃ δ : ℝ, 0 < δ ∧ rectIntegral (fun ζ => logDeriv W.L ζ) (1 - (δ : ℂ) * (1 + I))
      (1 + (δ : ℂ) * (1 + I)) = 2 * Real.pi * I * m := by
  have hne : ∃ s, W.L s ≠ 0 :=
    (analyticRank_ne_top_iff W).mp (by rw [hm]; exact ENat.natCast_ne_top m)
  obtain ⟨ε, hε, hiso⟩ := exists_isolated W.analytic hne 1
  refine ⟨ε / 2, half_pos hε, ?_⟩
  have hzw : (1 - ((ε / 2 : ℝ) : ℂ) * (1 + I)).re < (1 + ((ε / 2 : ℝ) : ℂ) * (1 + I)).re ∧
      (1 - ((ε / 2 : ℝ) : ℂ) * (1 + I)).im < (1 + ((ε / 2 : ℝ) : ℂ) * (1 + I)).im := by
    rw [re_corner, im_corner, re_corner', im_corner']
    constructor <;> linarith
  apply rectIntegral_logDeriv_eq W hm hzw
  · apply mem_openRect_of_bounds hzw
    rw [re_corner, im_corner, re_corner', im_corner']
    simp only [one_re, one_im]
    constructor <;> constructor <;> linarith
  · intro ζ hζ hL
    rw [closedRect, Complex.mem_reProdIm, re_corner, im_corner, re_corner', im_corner',
      Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at hζ
    apply hiso ζ _ hL
    rw [mem_closedBall_iff_norm]
    calc ‖ζ - 1‖ ≤ |(ζ - 1).re| + |(ζ - 1).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |ζ.re - 1| + |ζ.im| := by simp
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · rw [abs_le]; constructor <;> linarith [hζ.1.1, hζ.1.2]
          · rw [abs_le]; constructor <;> linarith [hζ.2.1, hζ.2.2]
      _ = ε := by ring

end Soma.Holonics.Millennium.BirchSwinnertonDyerWindingIsolated
