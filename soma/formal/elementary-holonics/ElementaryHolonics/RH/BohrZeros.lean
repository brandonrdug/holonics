import Mathlib
import ElementaryHolonics.RH.DescentApproximation

/-!
# RT5: the Dirichlet series `F_t` has zeros at every height in a fixed strip

`F_t` is entire with quadratic exponential growth; if it were zero-free, `log ‖F_t‖` would be the
real part of an entire function of quadratic growth, hence a quadratic polynomial by
Borel–Carathéodory and Cauchy's estimates, which the real axis refutes. Then Bohr's almost
periodicity carries the zero to every height.
-/

noncomputable section

namespace Soma.Holonics.RH.BohrZeros

open Real Set Filter Topology MeasureTheory
open Soma.Holonics.RH.DescentApproximation

/-! ## `F_t` is entire -/

theorem differentiable_Fterm (t : ℝ) (n : ℤ) : Differentiable ℂ (fun s => Fterm t s n) := by
  unfold Fterm
  split_ifs
  · exact differentiable_const _
  · fun_prop

/-- The one-sided bound: it uses only `−X ≤ Re s`. -/
theorem norm_Fterm_le' {t : ℝ} (ht : 0 < t) {X : ℝ} (hX0 : 0 ≤ X) {s : ℂ} (hX : -X ≤ s.re)
    (n : ℤ) :
    ‖Fterm t s n‖ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) := by
  by_cases hn : n = 0
  · subst hn
    simp [Fterm]
  have hL0 := log_abs_nonneg hn
  rw [norm_Fterm t s hn, ← Real.exp_add]
  have hx : -s.re ≤ X := by linarith
  calc Real.exp (-t * Real.log |(n : ℝ)| ^ 2 + -s.re * Real.log |(n : ℝ)|)
      ≤ Real.exp (X * Real.log |(n : ℝ)| - t * Real.log |(n : ℝ)| ^ 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hx hL0]
    _ ≤ Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t)) * |(n : ℝ)| ^ (-(3 / 2 : ℝ)) :=
        exp_neg_mul_log_sq_le ht hn hX0

theorem differentiable_Ft {t : ℝ} (ht : 0 < t) : Differentiable ℂ (Ft t) := by
  intro s
  set X : ℝ := |s.re| + 1 with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hU : IsOpen {z : ℂ | -X < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℤ, Fterm t w n) {z : ℂ | -X < z.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_Z32.mul_left
      (Real.exp (X ^ 2 / (2 * t) + 9 / (8 * t))))
      (fun n => (differentiable_Fterm t n).differentiableOn) hU
      (fun n w hw => norm_Fterm_le' ht hX0 (le_of_lt hw) n)
  have hmem : s ∈ {z : ℂ | -X < z.re} := by
    show -X < s.re
    linarith [neg_abs_le s.re]
  exact (hd.differentiableAt (hU.mem_nhds hmem))

/-! ## Growth -/

theorem Z32_pos : 0 < Z32 := by
  unfold Z32
  have h := le_hasSum summable_Z32.hasSum 1 (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  have : |((1 : ℤ) : ℝ)| ^ (-(3 / 2 : ℝ)) = 1 := by simp
  linarith

theorem norm_Ft_le {t : ℝ} (ht : 0 < t) (s : ℂ) :
    ‖Ft t s‖ ≤ Real.exp (s.re ^ 2 / (2 * t) + 9 / (8 * t)) * Z32 := by
  unfold Ft
  refine (norm_tsum_le_tsum_norm (summable_norm_Fterm ht s)).trans ?_
  have := tsum_norm_Fterm_le ht (X := |s.re|) (s := s) le_rfl
  rwa [sq_abs] at this

theorem log_norm_Ft_le {t : ℝ} (ht : 0 < t) (s : ℂ) (hF : Ft t s ≠ 0) :
    Real.log ‖Ft t s‖ ≤ s.re ^ 2 / (2 * t) + 9 / (8 * t) + Real.log Z32 := by
  have h := norm_Ft_le ht s
  have hpos : 0 < ‖Ft t s‖ := norm_pos_iff.mpr hF
  calc Real.log ‖Ft t s‖ ≤ Real.log (Real.exp (s.re ^ 2 / (2 * t) + 9 / (8 * t)) * Z32) :=
        Real.log_le_log hpos h
    _ = s.re ^ 2 / (2 * t) + 9 / (8 * t) + Real.log Z32 := by
        rw [Real.log_mul (Real.exp_pos _).ne' Z32_pos.ne', Real.log_exp]

/-! ## The real axis -/

/-- The real form of the main term at real `x`. -/
def Fr (t x : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else
    Real.exp (-t * Real.log |(n : ℝ)| ^ 2) * Real.exp (-x * Real.log |(n : ℝ)|)

theorem Fr_nonneg (t x : ℝ) (n : ℤ) : 0 ≤ Fr t x n := by
  unfold Fr
  split_ifs <;> positivity

theorem Fterm_ofReal (t x : ℝ) (n : ℤ) : Fterm t (x : ℂ) n = ((Fr t x n : ℝ) : ℂ) := by
  unfold Fterm Fr
  split_ifs with hn
  · simp
  · push_cast
    first | rfl | ring_nf

theorem norm_Fterm_eq_Fr (t x : ℝ) (n : ℤ) : ‖Fterm t (x : ℂ) n‖ = Fr t x n := by
  rw [Fterm_ofReal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Fr_nonneg t x n)]

theorem summable_Fr {t : ℝ} (ht : 0 < t) (x : ℝ) : Summable (Fr t x) := by
  have := summable_norm_Fterm ht (x : ℂ)
  simpa [norm_Fterm_eq_Fr] using this

theorem Ft_ofReal {t : ℝ} (ht : 0 < t) (x : ℝ) : Ft t (x : ℂ) = ((∑' n : ℤ, Fr t x n : ℝ) : ℂ) := by
  unfold Ft
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  exact Fterm_ofReal t x n

theorem norm_Ft_ofReal {t : ℝ} (ht : 0 < t) (x : ℝ) : ‖Ft t (x : ℂ)‖ = ∑' n : ℤ, Fr t x n := by
  rw [Ft_ofReal ht, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact tsum_nonneg (Fr_nonneg t x)

theorem Fr_one (t x : ℝ) : Fr t x 1 = 1 := by simp [Fr]
theorem Fr_neg_one (t x : ℝ) : Fr t x (-1) = 1 := by simp [Fr]
theorem Fr_two (t : ℝ) : Fr t 0 2 = Real.exp (-t * Real.log 2 ^ 2) := by
  simp [Fr]
theorem Fr_neg_two (t : ℝ) : Fr t 0 (-2) = Real.exp (-t * Real.log 2 ^ 2) := by
  simp [Fr]

/-- `‖F_t(0)‖ ≥ 2 + 2 e^{−t log² 2}`. -/
theorem norm_Ft_zero_ge {t : ℝ} (ht : 0 < t) :
    2 + 2 * Real.exp (-t * Real.log 2 ^ 2) ≤ ‖Ft t 0‖ := by
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  rw [← h0, norm_Ft_ofReal ht]
  have hs := summable_Fr ht 0
  have h := hs.sum_le_tsum ({1, -1, 2, -2} : Finset ℤ) (fun n _ => Fr_nonneg t 0 n)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fr_one, Fr_neg_one, Fr_two, Fr_neg_two] at h
  linarith

/-- `‖F_t(x)‖ ≥ 2` on the real axis. -/
theorem norm_Ft_ofReal_ge {t : ℝ} (ht : 0 < t) (x : ℝ) : 2 ≤ ‖Ft t (x : ℂ)‖ := by
  rw [norm_Ft_ofReal ht]
  have hs := summable_Fr ht x
  have h := hs.sum_le_tsum ({1, -1} : Finset ℤ) (fun n _ => Fr_nonneg t x n)
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, Fr_one, Fr_neg_one] at h
  linarith

/-- `‖F_t(x)‖ ≤ 2 + 2^{−x} ‖F_t(0)‖` for `x ≥ 0`. -/
theorem norm_Ft_ofReal_le {t : ℝ} (ht : 0 < t) {x : ℝ} (hx : 0 ≤ x) :
    ‖Ft t (x : ℂ)‖ ≤ 2 + (2 : ℝ) ^ (-x) * ‖Ft t 0‖ := by
  have h0 : ((0 : ℝ) : ℂ) = 0 := by simp
  rw [norm_Ft_ofReal ht, ← h0, norm_Ft_ofReal ht]
  -- pointwise: `Fr t x n ≤ g n + 2^{−x} Fr t 0 n` with `g` the indicator of `{1, −1}`
  set g : ℤ → ℝ := fun n => if n = 1 ∨ n = -1 then 1 else 0 with hg
  have hg_sum : ∑' n, g n = 2 := by
    rw [tsum_eq_sum (s := ({1, -1} : Finset ℤ)) (fun n hn => by
      simp only [hg]
      rw [if_neg]
      intro h
      rcases h with h | h <;> simp [h] at hn)]
    rw [Finset.sum_insert (by decide), Finset.sum_singleton]
    simp [hg]
    norm_num
  have hpt : ∀ n, Fr t x n ≤ g n + (2 : ℝ) ^ (-x) * Fr t 0 n := by
    intro n
    by_cases h1 : n = 1 ∨ n = -1
    · have hFr : Fr t x n = 1 := by rcases h1 with h | h <;> simp [h, Fr]
      have : 0 ≤ (2 : ℝ) ^ (-x) * Fr t 0 n := by
        have := Fr_nonneg t 0 n
        positivity
      simp only [hg, if_pos h1]
      linarith
    · simp only [hg, if_neg h1, zero_add]
      by_cases hn : n = 0
      · subst hn; simp [Fr]
      · unfold Fr
        rw [if_neg hn, if_neg hn]
        have hn2 : (2 : ℝ) ≤ |(n : ℝ)| := by
          push_neg at h1
          have : (2 : ℤ) ≤ |n| := by
            rcases le_or_gt 0 n with h | h
            · rw [abs_of_nonneg h]; omega
            · rw [abs_of_neg h]; omega
          exact_mod_cast this
        have hL2 : Real.log 2 ≤ Real.log |(n : ℝ)| := Real.log_le_log (by norm_num) hn2
        have e1 : Real.exp (-x * Real.log |(n : ℝ)|) ≤ (2 : ℝ) ^ (-x) := by
          rw [Real.rpow_def_of_pos (by norm_num)]
          apply Real.exp_le_exp.mpr
          nlinarith
        simp only [neg_zero, zero_mul, Real.exp_zero, mul_one]
        have := Real.exp_pos (-t * Real.log |(n : ℝ)| ^ 2)
        nlinarith
  have hsg : Summable g := by
    apply summable_of_ne_finset_zero (s := ({1, -1} : Finset ℤ))
    intro n hn
    simp only [hg]
    rw [if_neg]
    intro h
    rcases h with h | h <;> simp [h] at hn
  have hs0 := (summable_Fr ht 0).mul_left ((2 : ℝ) ^ (-x))
  calc ∑' n, Fr t x n ≤ ∑' n, (g n + (2 : ℝ) ^ (-x) * Fr t 0 n) :=
        hasSum_le hpt (summable_Fr ht x).hasSum (hsg.add hs0).hasSum
    _ = 2 + (2 : ℝ) ^ (-x) * ∑' n, Fr t 0 n := by
        rw [hsg.tsum_add hs0, hg_sum, tsum_mul_left]

end Soma.Holonics.RH.BohrZeros
