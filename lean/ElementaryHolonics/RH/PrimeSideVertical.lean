import Mathlib

/-!
# The right edge of the rectangle is the prime comb

On a vertical segment `σ + it`, `a ≤ t ≤ b`, with `σ > 1`, the logarithmic derivative of zeta is
the Dirichlet series of the von Mangoldt function, and the series converges absolutely and
uniformly on the segment.  Hence for any continuous weight `h`, the integral of `h · (−ζ′/ζ)` along
the segment is the sum over prime powers of the weighted integrals of the terms: the right edge
of the explicit-formula rectangle is the prime comb, read term by term.
-/

noncomputable section

namespace Soma.Holonics.RH.PrimeSideVertical

open Complex MeasureTheory intervalIntegral Set
open scoped Interval

/-- The von Mangoldt coefficients as a complex sequence. -/
abbrev vonMangoldtC : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The point `σ + it` of the vertical segment. -/
def edge (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * I

@[simp] theorem re_edge (σ t : ℝ) : (edge σ t).re = σ := by simp [edge]

theorem continuous_edge (σ : ℝ) : Continuous (edge σ) := by
  unfold edge
  fun_prop

/-- The von Mangoldt term is continuous in `s`. -/
theorem continuous_term (n : ℕ) : Continuous fun s : ℂ => LSeries.term vonMangoldtC s n := by
  unfold LSeries.term
  by_cases hn : n = 0
  · simp [hn]
    exact continuous_const
  · simp only [hn, ↓reduceIte]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    apply Continuous.div continuous_const (continuous_id.const_cpow (Or.inl hn'))
    intro s
    exact fun h => hn' ((cpow_eq_zero_iff _ _).mp h).1

/-- The norm of a term depends only on the real part. -/
theorem norm_term_edge (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term vonMangoldtC (edge σ t) n‖ = ‖LSeries.term vonMangoldtC (σ : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, re_edge, ofReal_re]

/-- Absolute convergence of the von Mangoldt series at real part `σ > 1`. -/
theorem summable_norm_term {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n => ‖LSeries.term vonMangoldtC (σ : ℂ) n‖ := by
  have h : LSeriesSummable vonMangoldtC (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  exact h.norm

/-- **The right edge is the prime comb.** For a continuous weight `h` and `σ > 1`, the weighted
integral of `−ζ′/ζ` along the segment `σ + it`, `t ∈ [a, b]`, is the sum over `n` of the weighted
integrals of the von Mangoldt terms. -/
theorem hasSum_integral_term {h : ℂ → ℂ} (hh : Continuous h) {σ : ℝ} (hσ : 1 < σ) (a b : ℝ) :
    HasSum (fun n => ∫ t in a..b, h (edge σ t) * LSeries.term vonMangoldtC (edge σ t) n)
      (∫ t in a..b, h (edge σ t) * (-(deriv riemannZeta (edge σ t) / riemannZeta (edge σ t)))) := by
  -- the weight is bounded on the segment
  obtain ⟨C, hC⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
    (hh.comp (continuous_edge σ)).continuousOn
  have hC0 : 0 ≤ C := by
    have := hC a left_mem_uIcc
    exact (norm_nonneg _).trans this
  -- identify the limit
  have hlim : ∀ t, (-(deriv riemannZeta (edge σ t) / riemannZeta (edge σ t))) =
      LSeries vonMangoldtC (edge σ t) := by
    intro t
    have := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := edge σ t)
      (by simpa using hσ)
    rw [neg_div] at this
    exact this.symm
  simp_rw [hlim]
  refine hasSum_integral_of_dominated_convergence
    (fun n _ => C * ‖LSeries.term vonMangoldtC (σ : ℂ) n‖) ?_ ?_ ?_ ?_ ?_
  · intro n
    exact Continuous.aestronglyMeasurable (Continuous.mul (hh.comp (continuous_edge σ)) ((continuous_term n).comp (continuous_edge σ)))
  · intro n
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [norm_mul, norm_term_edge]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact hC t (uIoc_subset_uIcc ht)
  · exact Filter.Eventually.of_forall fun t _ => (summable_norm_term hσ).mul_left C
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun t _ => ?_
    have hs : LSeriesSummable vonMangoldtC (edge σ t) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
    exact hs.hasSum.mul_left _

end Soma.Holonics.RH.PrimeSideVertical
