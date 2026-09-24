import ElementaryHolonics.RH.ArchimedeanReceiver
import Mathlib.Tactic

/-!
# The paired archimedean mode has both spectral signs

Expanding the denominator of the exact archimedean receiver gives paired
modes with decay rates 2m + 1/2 and 2m + 2. For an autocorrelation current,
the real translation-frequency symbol of the m-th paired mode is

  2 lambda / (lambda^2 + omega^2) - 1 / (m + 1),

where lambda = 2m + 1/2. The two summands are kept together; summing either
unpaired arm over m would lose the cancellation at the common denominator.

The finite algebra below proves that every mode has a positive low-frequency
face and a negative high-frequency face. It does not prove a Fourier
representation theorem for the complete archimedean receiver or Weil
positivity.
-/

noncomputable section

namespace Soma.Holonics.RH.ArchimedeanModeSign

open Soma.Holonics.RH.ArchimedeanReceiver

/-- The m-th paired summand of the geometric archimedean denominator.
The two arms share one mode and must be summed together. -/
def pairedNumerator (T : ExplicitFormulaReceiver.WeilTestFunction)
    (m : ℕ) (x : ℝ) : ℂ :=
  ((Real.exp (-(2 * (m : ℝ) + 1 / 2) * x) : ℝ) : ℂ) * evenKernel T x -
    ((Real.exp (-(2 * (m : ℝ) + 2) * x) : ℝ) : ℂ) * T.arithmeticKernel 0

private theorem pairedNumerator_eq_geometric
    (T : ExplicitFormulaReceiver.WeilTestFunction) (m : ℕ) (x : ℝ) :
    pairedNumerator T m x =
      (((Real.exp (-2 * x) : ℝ) : ℂ) ^ m) *
        (((Real.exp (-x / 2) : ℝ) : ℂ) * evenKernel T x -
          ((Real.exp (-2 * x) : ℝ) : ℂ) * T.arithmeticKernel 0) := by
  have hhalf :
      Real.exp (-(2 * (m : ℝ) + 1 / 2) * x) =
        Real.exp (-2 * x) ^ m * Real.exp (-x / 2) := by
    calc
      Real.exp (-(2 * (m : ℝ) + 1 / 2) * x)
          = Real.exp ((m : ℝ) * (-2 * x) + (-x / 2)) := by congr 1; ring
      _ = Real.exp ((m : ℝ) * (-2 * x)) * Real.exp (-x / 2) := Real.exp_add _ _
      _ = Real.exp (-2 * x) ^ m * Real.exp (-x / 2) := by
        rw [Real.exp_nat_mul]
  have hwhole :
      Real.exp (-(2 * (m : ℝ) + 2) * x) =
        Real.exp (-2 * x) ^ m * Real.exp (-2 * x) := by
    calc
      Real.exp (-(2 * (m : ℝ) + 2) * x)
          = Real.exp ((m : ℝ) * (-2 * x) + (-2 * x)) := by congr 1; ring
      _ = Real.exp ((m : ℝ) * (-2 * x)) * Real.exp (-2 * x) := Real.exp_add _ _
      _ = Real.exp (-2 * x) ^ m * Real.exp (-2 * x) := by
        rw [Real.exp_nat_mul]
  unfold pairedNumerator
  rw [hhalf, hwhole]
  push_cast
  ring

/-- Exact finite geometric partition of the source archimedean numerator.
It is valid even at x = 0 because no division has been introduced. -/
theorem pairedNumerator_finite_partition
    (T : ExplicitFormulaReceiver.WeilTestFunction) (N : ℕ) (x : ℝ) :
    (1 - ((Real.exp (-2 * x) : ℝ) : ℂ)) *
      (∑ m ∈ Finset.range N, pairedNumerator T m x) =
    (1 - (((Real.exp (-2 * x) : ℝ) : ℂ) ^ N)) *
      (((Real.exp (-x / 2) : ℝ) : ℂ) * evenKernel T x -
        ((Real.exp (-2 * x) : ℝ) : ℂ) * T.arithmeticKernel 0) := by
  simp_rw [pairedNumerator_eq_geometric]
  rw [← Finset.sum_mul]
  calc
    (1 - ((Real.exp (-2 * x) : ℝ) : ℂ)) *
      ((∑ m ∈ Finset.range N, (((Real.exp (-2 * x) : ℝ) : ℂ) ^ m)) *
        (((Real.exp (-x / 2) : ℝ) : ℂ) * evenKernel T x -
          ((Real.exp (-2 * x) : ℝ) : ℂ) * T.arithmeticKernel 0))
      =
      ((∑ m ∈ Finset.range N, (((Real.exp (-2 * x) : ℝ) : ℂ) ^ m)) *
        (1 - ((Real.exp (-2 * x) : ℝ) : ℂ))) *
        (((Real.exp (-x / 2) : ℝ) : ℂ) * evenKernel T x -
          ((Real.exp (-2 * x) : ℝ) : ℂ) * T.arithmeticKernel 0) := by ring
    _ = _ := by rw [geom_sum_mul_neg]

def decay (m : ℕ) : ℝ := 2 * (m : ℝ) + 1 / 2
def scale (m : ℕ) : ℝ := (m : ℝ) + 1

def pairedSymbol (m : ℕ) (ω : ℝ) : ℝ :=
  2 * decay m / (decay m ^ 2 + ω ^ 2) - 1 / scale m

/-- One positive denominator exposes the exact sign-changing numerator
of each paired archimedean mode. Its zero set is the source-specific
frequency threshold, not a count of positive series coefficients. -/
theorem pairedSymbol_commonDenominator (m : ℕ) (ω : ℝ) :
    pairedSymbol m ω =
      ((3 / 2 : ℝ) * decay m - ω ^ 2) /
        (scale m * (decay m ^ 2 + ω ^ 2)) := by
  have hl : 0 < decay m := by unfold decay; positivity
  have hq : 0 < scale m := by unfold scale; positivity
  have hden : 0 < decay m ^ 2 + ω ^ 2 := by positivity
  have hdelta : 2 * scale m - decay m = 3 / 2 := by
    simp [decay, scale]
    ring
  unfold pairedSymbol
  field_simp
  nlinarith [hdelta]

/-- The paired archimedean mode's positive sector is precisely the
frequency interval whose squared frequency is below its threshold. -/
theorem pairedSymbol_nonneg_iff (m : ℕ) (ω : ℝ) :
    0 ≤ pairedSymbol m ω ↔ ω ^ 2 ≤ (3 / 2 : ℝ) * decay m := by
  rw [pairedSymbol_commonDenominator]
  have hden : 0 < scale m * (decay m ^ 2 + ω ^ 2) :=
    mul_pos (by unfold scale; positivity) (by
      have hl : 0 < decay m := by unfold decay; positivity
      positivity)
  constructor
  · intro h
    have hn : 0 ≤ (3 / 2 : ℝ) * decay m - ω ^ 2 := by
      rcases div_nonneg_iff.mp h with h | h
      · exact h.1
      · exact False.elim ((not_le_of_gt hden) h.2)
    linarith
  · intro h
    exact div_nonneg (by linarith) hden.le

theorem decay_pos (m : ℕ) : 0 < decay m := by
  unfold decay
  positivity

theorem scale_pos (m : ℕ) : 0 < scale m := by
  unfold scale
  positivity

theorem pairedSymbol_zero_pos (m : ℕ) : 0 < pairedSymbol m 0 := by
  have hl : 0 < decay m := decay_pos m
  have hq : 0 < scale m := scale_pos m
  have hid : 2 * scale m - decay m = 3 / 2 := by
    simp [decay, scale]
    ring
  unfold pairedSymbol
  have hden : 0 < decay m ^ 2 + (0 : ℝ) ^ 2 := by positivity
  have hprod : 0 < (decay m) * (2 * scale m - decay m) := by
    rw [hid]
    positivity
  apply (sub_pos).2
  apply (div_lt_div_iff₀ hq hden).2
  nlinarith

theorem pairedSymbol_high_neg (m : ℕ) :
    pairedSymbol m (2 * scale m) < 0 := by
  have hl : 0 < decay m := decay_pos m
  have hq : 0 < scale m := scale_pos m
  have hden : 0 < decay m ^ 2 + (2 * scale m) ^ 2 := by positivity
  unfold pairedSymbol
  apply (sub_neg).2
  apply (div_lt_div_iff₀ hden hq).2
  nlinarith [sq_nonneg (decay m - scale m), sq_pos_of_pos hq]

theorem pairedSymbol_changes_sign (m : ℕ) :
    0 < pairedSymbol m 0 ∧ pairedSymbol m (2 * scale m) < 0 :=
  ⟨pairedSymbol_zero_pos m, pairedSymbol_high_neg m⟩

/-- The first mode gives exact, opposing values at two frequencies. -/
theorem firstMode_zero : pairedSymbol 0 0 = 3 := by
  norm_num [pairedSymbol, decay, scale]

theorem firstMode_two : pairedSymbol 0 2 = -(13 / 17 : ℝ) := by
  norm_num [pairedSymbol, decay, scale]

#print axioms pairedSymbol_zero_pos
#print axioms pairedSymbol_commonDenominator
#print axioms pairedSymbol_nonneg_iff
#print axioms pairedSymbol_high_neg
#print axioms firstMode_two
#print axioms pairedNumerator_finite_partition

end Soma.Holonics.RH.ArchimedeanModeSign
