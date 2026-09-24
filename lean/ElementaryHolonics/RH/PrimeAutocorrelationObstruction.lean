import ElementaryHolonics.RH.ExplicitFormulaReceiver

/-!
# A prime atom is not a positive Weil-square operator

The von Mangoldt weight at two is positive. This does not make its pairing
with every Weil autocorrelation positive: an autocorrelation can have a
negative value at a nonzero lag. The exact two-site generator (1,-1)
already supplies a counterexample to termwise positivity.

This finite theorem is a source-qualified obstruction, not a constructed
WeilTestFunction and not a counterexample to the complete Weil form.
The polar and archimedean receivers provide diagonal terms that the
prime atom alone does not carry.
-/

namespace Soma.Holonics.RH.PrimeAutocorrelationObstruction

open ArithmeticFunction
open Soma.Holonics.RH.ExplicitFormulaReceiver

/-- The finite generator whose two occupied sites have opposite phase. -/
def opposedGenerator (k : ℤ) : ℝ :=
  if k = 0 then 1 else if k = 1 then -1 else 0

/-- Its exact autocorrelation; the two summands are its two source sites. -/
def twoSiteCorrelation (k : ℤ) : ℝ :=
  opposedGenerator 0 * opposedGenerator k +
    opposedGenerator 1 * opposedGenerator (1 + k)

/-- The same two sites with aligned rather than opposed generator phases. -/
def alignedGenerator (k : ℤ) : ℝ :=
  if k = 0 then 1 else if k = 1 then 1 else 0

def alignedTwoSiteCorrelation (k : ℤ) : ℝ :=
  alignedGenerator 0 * alignedGenerator k +
    alignedGenerator 1 * alignedGenerator (1 + k)

theorem twoSiteCorrelation_at_zero : twoSiteCorrelation 0 = 2 := by
  norm_num [twoSiteCorrelation, opposedGenerator]

theorem twoSiteCorrelation_at_one : twoSiteCorrelation 1 = -1 := by
  simp [twoSiteCorrelation, opposedGenerator]

theorem twoSiteCorrelation_at_neg_one : twoSiteCorrelation (-1) = -1 := by
  simp [twoSiteCorrelation, opposedGenerator]

/-- The resulting two-receiver Gram matrix is positive semidefinite.
Its off-diagonal entry is nevertheless negative. -/
theorem twoSiteGram_nonnegative (x y : ℝ) :
    0 ≤ twoSiteCorrelation 0 * (x ^ 2 + y ^ 2) +
      2 * twoSiteCorrelation 1 * x * y := by
  rw [twoSiteCorrelation_at_zero, twoSiteCorrelation_at_one]
  nlinarith [sq_nonneg (x - y), sq_nonneg x, sq_nonneg y]

theorem alignedTwoSiteGram_nonnegative (x y : ℝ) :
    0 ≤ alignedTwoSiteCorrelation 0 * (x ^ 2 + y ^ 2) +
      2 * alignedTwoSiteCorrelation 1 * x * y := by
  have h0 : alignedTwoSiteCorrelation 0 = 2 := by
    norm_num [alignedTwoSiteCorrelation, alignedGenerator]
  have h1 : alignedTwoSiteCorrelation 1 = 1 := by
    norm_num [alignedTwoSiteCorrelation, alignedGenerator]
  rw [h0, h1]
  nlinarith [sq_nonneg (x + y), sq_nonneg x, sq_nonneg y]

/-- The first prime address has positive weight, with no floating-point input. -/
theorem firstPrimeWeight_pos :
    0 < vonMangoldt 2 / Real.sqrt 2 := by
  rw [vonMangoldt_apply_prime Nat.prime_two]
  exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.2 (by norm_num))

/-- Both orientations of the first prime atom read the negative unit-lag
autocorrelation. Thus positivity of Lambda(2) cannot be applied termwise
to a generic Weil square. -/
theorem firstPrimeAtom_negative :
    (vonMangoldt 2 / Real.sqrt 2) *
      (twoSiteCorrelation 1 + twoSiteCorrelation (-1)) < 0 := by
  rw [twoSiteCorrelation_at_one, twoSiteCorrelation_at_neg_one]
  nlinarith [firstPrimeWeight_pos]

/-- Reversing the relative generator phase reverses the prime contact.
Thus neither sign of the isolated prime receiver is positive on all
two-site autocorrelations. -/
theorem firstPrimeAtom_positive :
    0 < (vonMangoldt 2 / Real.sqrt 2) *
      (alignedTwoSiteCorrelation 1 + alignedTwoSiteCorrelation (-1)) := by
  have h1 : alignedTwoSiteCorrelation 1 = 1 := by
    norm_num [alignedTwoSiteCorrelation, alignedGenerator]
  have hm1 : alignedTwoSiteCorrelation (-1) = 1 := by
    norm_num [alignedTwoSiteCorrelation, alignedGenerator]
  rw [h1, hm1]
  exact mul_pos firstPrimeWeight_pos (by norm_num)

/-- A diagonal material supplied by the other places is enough for this
first-prime contact exactly when it meets the contact weight. This is a
finite local criterion; the full Weil receiver has infinitely many
prime-power contacts and a nonlocal archimedean part. -/
def completedTwoSiteEnergy (d w x y : ℝ) : ℝ :=
  d * (x ^ 2 + y ^ 2) - 2 * w * x * y

theorem completedTwoSiteEnergy_nonnegative_iff (w d : ℝ) (hw : 0 ≤ w) :
    (∀ x y : ℝ, 0 ≤ completedTwoSiteEnergy d w x y) ↔ w ≤ d := by
  constructor
  · intro h
    have h11 := h 1 1
    unfold completedTwoSiteEnergy at h11
    nlinarith
  · intro hd x y
    have hsum : 0 ≤ x ^ 2 + y ^ 2 :=
      add_nonneg (sq_nonneg x) (sq_nonneg y)
    have hdiff : 0 ≤ (x - y) ^ 2 := sq_nonneg _
    calc
      0 ≤ (d - w) * (x ^ 2 + y ^ 2) + w * (x - y) ^ 2 :=
        add_nonneg (mul_nonneg (sub_nonneg.mpr hd) hsum) (mul_nonneg hw hdiff)
      _ = completedTwoSiteEnergy d w x y := by unfold completedTwoSiteEnergy; ring

theorem firstPrimeDiagonalThreshold (d : ℝ) :
    (∀ x y : ℝ,
      0 ≤ completedTwoSiteEnergy d (vonMangoldt 2 / Real.sqrt 2) x y) ↔
        vonMangoldt 2 / Real.sqrt 2 ≤ d :=
  completedTwoSiteEnergy_nonnegative_iff _ _ firstPrimeWeight_pos.le

/-- At cutoff two the actual finite-place receiver reads only the two
opposite logarithmic orientations at the first prime address. -/
theorem truncatedPrimeReceiver_at_two (T : WeilTestFunction) :
    truncatedPrimeReceiver T 2 =
      (((Real.log 2 / Real.sqrt 2 : ℝ) : ℂ)) *
        (T.arithmeticKernel (Real.log 2) +
          T.arithmeticKernel (-Real.log 2)) := by
  unfold truncatedPrimeReceiver
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hIcc]
  norm_num [vonMangoldt_apply_prime Nat.prime_two, vonMangoldt_apply_one]

section Audit

#print axioms twoSiteGram_nonnegative
#print axioms alignedTwoSiteGram_nonnegative
#print axioms firstPrimeAtom_negative
#print axioms firstPrimeAtom_positive
#print axioms completedTwoSiteEnergy_nonnegative_iff
#print axioms truncatedPrimeReceiver_at_two

end Audit

end Soma.Holonics.RH.PrimeAutocorrelationObstruction
