import ElementaryHolonics.Millennium.BirchSwinnertonDyerFiniteRank
import ElementaryHolonics.RH.RectangleArgumentPrinciple
import ElementaryHolonics.RH.FactorizationMultiplicity
import ElementaryHolonics.RH.ZeroFactorizationExists

/-!
# The analytic rank is the winding of `L′/L` around the centre

The analytic rank of an `LDatum` is the analytic order of its entire `L` at the centre `1`.
Through the rectangle argument principle and the identification of factorization
multiplicities with analytic orders, it is the winding number of `L′/L` around any rectangle
that contains `1` in its interior and no other zero of `L` in its closure:
`∮ L′/L = 2πi · analyticRank`.  This is the same receiver that returns the zero comb of `ξ`:
the analytic rank is a comb multiplicity, read by a contour.
-/

open Complex Metric Set Finset
open scoped Classical
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.BirchSwinnertonDyerFiniteRank
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleArgumentPrinciple
open Soma.Holonics.RH.FactorizationMultiplicity
open Soma.Holonics.RH.ZeroFactorizationExists

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerWinding

variable {n : ℕ}

/-- The zeros of a factorization of an entire function are its zeros. -/
theorem eq_zero_of_mem_zeros {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (Z : ZeroFactorization f z₀ r) {ρ : ℂ} (hρ : ρ ∈ Z.zeros) : f ρ = 0 := by
  have hρr : ρ ∈ ball z₀ r := by
    have := Z.zeros_mem ρ hρ
    rw [mem_closedBall_iff_norm] at this
    rw [mem_ball_iff_norm]
    linarith
  rw [Z.factor ρ hρr]
  apply mul_eq_zero_of_left
  exact Finset.prod_eq_zero hρ (by
    rw [sub_self, zero_pow (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ hρ))])

/-- Every closed rectangle lies in a half disc about any given point. -/
theorem closedRect_subset_ball_of_radius (z w s₀ : ℂ) :
    closedRect z w ⊆ ball s₀ (2 * (2 * (‖z‖ + ‖w‖) + ‖s₀‖ + 1) / 2) := by
  intro ζ hζ
  rw [closedRect, Complex.mem_reProdIm, Set.mem_uIcc, Set.mem_uIcc] at hζ
  have hzr := abs_le.mp (Complex.abs_re_le_norm z)
  have hwr := abs_le.mp (Complex.abs_re_le_norm w)
  have hzi := abs_le.mp (Complex.abs_im_le_norm z)
  have hwi := abs_le.mp (Complex.abs_im_le_norm w)
  have hre : |ζ.re| ≤ ‖z‖ + ‖w‖ := by
    rw [abs_le]
    rcases hζ.1 with h | h <;> constructor <;> linarith [h.1, h.2, norm_nonneg z, norm_nonneg w]
  have him : |ζ.im| ≤ ‖z‖ + ‖w‖ := by
    rw [abs_le]
    rcases hζ.2 with h | h <;> constructor <;> linarith [h.1, h.2, norm_nonneg z, norm_nonneg w]
  rw [mem_ball_iff_norm]
  calc ‖ζ - s₀‖ ≤ ‖ζ‖ + ‖s₀‖ := norm_sub_le _ _
    _ ≤ (|ζ.re| + |ζ.im|) + ‖s₀‖ := by gcongr; exact Complex.norm_le_abs_re_add_abs_im ζ
    _ < 2 * (2 * (‖z‖ + ‖w‖) + ‖s₀‖ + 1) / 2 := by linarith

/-- **The analytic rank is the winding of `L′/L` around the centre.**  For a rectangle containing
`1` in its interior on whose closure `L` vanishes only at `1`,
`∮ L′/L = 2πi · analyticRank`. -/
theorem rectIntegral_logDeriv_eq (W : LDatum n) {m : ℕ} (hm : analyticRank W = m)
    {z w : ℂ} (hzw : z.re < w.re ∧ z.im < w.im) (h1 : (1 : ℂ) ∈ openRect z w)
    (hunique : ∀ ζ ∈ closedRect z w, W.L ζ = 0 → ζ = 1) :
    rectIntegral (fun ζ => logDeriv W.L ζ) z w = 2 * Real.pi * I * m := by
  have hne : ∃ s, W.L s ≠ 0 :=
    (analyticRank_ne_top_iff W).mp (by rw [hm]; exact ENat.natCast_ne_top m)
  obtain ⟨s₀, hs₀⟩ := hne
  set r : ℝ := 2 * (2 * (‖z‖ + ‖w‖) + ‖s₀‖ + 1) with hr_def
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrect : closedRect z w ⊆ ball s₀ (r / 2) := closedRect_subset_ball_of_radius z w s₀
  obtain ⟨Z⟩ := exists_zeroFactorization W.analytic hr hs₀
  have h1c : (1 : ℂ) ∈ closedRect z w := openRect_subset_closedRect z w h1
  have h1b : (1 : ℂ) ∈ ball s₀ (r / 2) := hrect h1c
  have hzero_eq : ∀ ρ ∈ Z.zeros, ρ ∈ closedRect z w → ρ = 1 :=
    fun ρ hρ hc => hunique ρ hc (eq_zero_of_mem_zeros hr Z hρ)
  have hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w := by
    intro ρ hρ hb
    have := hzero_eq ρ hρ (boundaryRect_subset_closedRect z w hb)
    rw [this] at hb
    exact hb.2 h1
  have hmain := rectIntegral_mul_logDeriv Z hr hzw hrect (h := fun _ => (1 : ℂ))
    (differentiableOn_const 1) hbd
  simp only [mul_one, one_mul] at hmain
  rw [hmain]
  congr 1
  by_cases hmem : (1 : ℂ) ∈ Z.zeros
  · rw [Finset.sum_eq_single_of_mem (1 : ℂ) hmem (fun ρ hρ hne1 => by
      rw [if_neg]
      intro hin
      exact hne1 (hzero_eq ρ hρ (openRect_subset_closedRect z w hin))), if_pos h1]
    have := analyticOrderAt_eq_mult Z W.analytic.differentiableOn hr hmem h1b
    have hm' : (m : ℕ∞) = Z.mult 1 := by
      rw [← this]
      exact hm.symm
    exact_mod_cast hm'.symm
  · have h0 := analyticOrderAt_eq_zero_of_notMem Z W.analytic.differentiableOn hr hmem h1b
    have hm0 : m = 0 := by
      have : (m : ℕ∞) = 0 := by
        rw [← hm]
        exact h0
      exact_mod_cast this
    rw [hm0, Finset.sum_eq_zero]
    · simp
    · intro ρ hρ
      rw [if_neg]
      intro hin
      exact hmem ((hzero_eq ρ hρ (openRect_subset_closedRect z w hin)) ▸ hρ)

end Soma.Holonics.Millennium.BirchSwinnertonDyerWinding
