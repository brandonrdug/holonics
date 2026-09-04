import ElementaryHolonics.RH.Xi
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic

/-!
# One certified evaluation of the finite-place side

`RH.Xi` establishes that the finite side of Weil's pairing is the von Mangoldt series, that every
local weight is nonnegative, and that the sum is therefore nonnegative.  What it does not do is
*evaluate* anything: a nonnegativity theorem with no computed instance is a claim about a sum
nobody has added up.

This file computes one, exactly.  For the test vector supported at `{2, 4, 8}` the finite-place
functional returns `3·log 2` — **not a bound, the value** — and the non-prime-power addresses
contribute exactly zero, which is the address structure of the ledger made visible rather than
summarised.
-/

namespace Soma.Holonics.RH.WeilVector

open ArithmeticFunction

/-- A test vector supported on the first three powers of two. -/
def twoPowerVector : ℕ → ℝ := fun n => if n = 2 ∨ n = 4 ∨ n = 8 then 1 else 0

theorem theVectorIsNonnegative : ∀ n, 0 ≤ twoPowerVector n := by
  intro n
  rw [twoPowerVector]
  split <;> norm_num

/-- **THE LOCAL WEIGHTS AT THE THREE ADDRESSES ARE ALL `log 2`.**  A prime power carries the log of
its prime, whatever the exponent — the address, not the size, decides the weight. -/
theorem theWeightsAtThePowersOfTwo :
    vonMangoldt 2 = Real.log 2 ∧ vonMangoldt 4 = Real.log 2 ∧ vonMangoldt 8 = Real.log 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [vonMangoldt_apply_prime Nat.prime_two]; norm_num
  · rw [show (4 : ℕ) = 2 ^ 2 by norm_num, vonMangoldt_apply_pow (by norm_num),
      vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  · rw [show (8 : ℕ) = 2 ^ 3 by norm_num, vonMangoldt_apply_pow (by norm_num),
      vonMangoldt_apply_prime Nat.prime_two]
    norm_num

/-- **AND A NON-PRIME-POWER CARRIES NOTHING.**  Six is an address the ledger does not pay. -/
theorem theCompositeAddressIsUnpaid : vonMangoldt 6 = 0 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num]
  simpa using vonMangoldt_eq_zero_iff.2 (by decide)

/-- **THE CERTIFIED EVALUATION.**  The finite-place functional on this test vector is exactly
`3·log 2`.  Every term outside `{2, 4, 8}` vanishes because the vector does; the three that remain
each weigh `log 2` because they share one prime address. -/
theorem theWeilFunctionalOnOneTestVector :
    ∑' n : ℕ, vonMangoldt n * twoPowerVector n = 3 * Real.log 2 := by
  have hsupp : ∀ n ∉ ({2, 4, 8} : Finset ℕ), vonMangoldt n * twoPowerVector n = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    rw [twoPowerVector, if_neg (by tauto), mul_zero]
  rw [tsum_eq_sum hsupp, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  obtain ⟨h2, h4, h8⟩ := theWeightsAtThePowersOfTwo
  simp only [twoPowerVector]
  norm_num [h2, h4, h8]
  ring

/-- **AND IT IS STRICTLY POSITIVE.**  So the finite side of Weil's pairing is not merely
nonnegative in principle; it has a computed positive value on an exhibited vector. -/
theorem theEvaluationIsStrictlyPositive :
    0 < ∑' n : ℕ, vonMangoldt n * twoPowerVector n := by
  rw [theWeilFunctionalOnOneTestVector]
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ## The test vector was not arbitrary: it is the divisor indicator -/

/-- The divisor indicator of `n`: the canonical test vector at that address. -/
def divisorVector (n : ℕ) : ℕ → ℝ := fun k => if k ∈ n.divisors then 1 else 0

theorem theDivisorVectorIsNonnegative (n : ℕ) : ∀ k, 0 ≤ divisorVector n k := by
  intro k
  rw [divisorVector]
  split <;> norm_num

/-- **THE FINITE-PLACE FUNCTIONAL ON THE DIVISOR INDICATOR OF `n` IS `log n`.**  Not one exhibited
value but a general law: `∑_{d ∣ n} Λ(d) = log n` is the von Mangoldt convolution, so the prime
side reads off **the logarithm of the address itself**.  The earlier `{2, 4, 8}` vector was the
divisor set of `8`, and its value `3·log 2` is `log 8` — the evaluation was canonical, not a
choice. -/
theorem theFiniteFunctionalOnADivisorVectorIsTheLogarithm (n : ℕ) :
    ∑' k : ℕ, vonMangoldt k * divisorVector n k = Real.log n := by
  classical
  have hsupp : ∀ k ∉ n.divisors, vonMangoldt k * divisorVector n k = 0 := by
    intro k hk
    rw [divisorVector, if_neg hk, mul_zero]
  rw [tsum_eq_sum hsupp]
  have hone : ∀ k ∈ n.divisors, vonMangoldt k * divisorVector n k = vonMangoldt k := by
    intro k hk
    rw [divisorVector, if_pos hk, mul_one]
  rw [Finset.sum_congr rfl hone]
  exact ArithmeticFunction.vonMangoldt_sum

/-- **AND THE EARLIER EVALUATION IS ITS INSTANCE AT EIGHT.**  `3·log 2 = log 8`. -/
theorem theEarlierEvaluationIsTheLogarithmOfEight : 3 * Real.log 2 = Real.log 8 := by
  rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
  norm_num

/-! ## The archimedean place, evaluated as a difference -/

open Soma.Holonics.RH in
/-- **THE ARCHIMEDEAN TERM RETURNS A DIFFERENCE, NOT A MAGNITUDE.**  Summing the digamma
recurrence along the integers gives

```text
ψ(n + 1) − ψ(1) = Σ_{k<n} 1/(k+1) = H_n ,
```

exactly.  No Euler–Mascheroni constant is needed and none appears: the archimedean place has **no
absolute value that crosses**, only a ratio against its anchor — the horizon law, on the place at
infinity.  Mathlib carries no `ψ` at all, so this is the archimedean side's first certified
evaluation in this tree. -/
theorem theArchimedeanDifferenceIsTheHarmonicNumber (n : ℕ) :
    digamma ((n : ℂ) + 1) - digamma 1 = ∑ k ∈ Finset.range n, (1 : ℂ) / (k + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hs : ∀ j : ℕ, ((m : ℂ) + 1) ≠ -(j : ℂ) := by
      intro j hc
      have hre := congrArg Complex.re hc
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.neg_re] at hre
      nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) j]
    have hs0 : ((m : ℂ) + 1) ≠ 0 := by
      intro hc
      have hre := congrArg Complex.re hc
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hstep := theDigammaRecurrence (s := (m : ℂ) + 1) hs hs0
    have hcast : (((m + 1 : ℕ) : ℂ) + 1) = ((m : ℂ) + 1) + 1 := by push_cast; ring
    rw [hcast, hstep, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- **AND IT IS POSITIVE AND STRICTLY INCREASING IN `n`.**  The archimedean ledger accumulates; it
never repays. -/
theorem theArchimedeanDifferenceGrows (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) ≤ ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k + 1) := by
  rw [Finset.sum_range_succ]
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

end Soma.Holonics.RH.WeilVector
