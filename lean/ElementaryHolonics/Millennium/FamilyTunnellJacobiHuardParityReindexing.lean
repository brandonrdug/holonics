import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource

/-!
# The exact parity reindexing in the Huard level-two source

The congruence receiver `x ≡ y (mod 2)` is resolved into the even-quotient
and odd-quotient divisor fibres.  The even fibre at `m` is exactly the
ordinary divisor population at `m / 2` when that address exists.  The two
mixed Cauchy currents are `W₂(n)` and the even/even intersection is the
level-one current at `n / 2`.  Thus no floor-division value is used when the
half-address fibre is empty.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardParityReindexing

open Finset PowerSeries
open Soma.Holonics.Mathematics.PowerSeriesExactDilation
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource

/-- The divisor current whose retained complementary quotient has parity
`epsilon`.  Only `epsilon = 0,1` is used below. -/
def quotientParityDivisorCurrent (epsilon n : ℕ) : ℤ :=
  ∑ a ∈ n.divisors,
    if (n / a) % 2 = epsilon then (a : ℤ) else 0

/-- Every quotient of a positive divisor has exactly one of the two parity
faces, so their currents reconstruct the complete divisor current. -/
theorem quotientParity_zero_add_one (n : ℕ) :
    quotientParityDivisorCurrent 0 n +
        quotientParityDivisorCurrent 1 n =
      ordinaryDivisorCurrent n := by
  rw [quotientParityDivisorCurrent, quotientParityDivisorCurrent,
    ordinaryDivisorCurrent, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hmod : (n / a) % 2 = 0 ∨ (n / a) % 2 = 1 := by omega
  rcases hmod with hmod | hmod <;> simp [hmod]

/-- The even-quotient divisor fibre of `n` is exactly the complete divisor
population of the half-address when that address exists. -/
theorem quotientParity_zero_eq_half (n : ℕ) :
    quotientParityDivisorCurrent 0 n =
      if 2 ∣ n then ordinaryDivisorCurrent (n / 2) else 0 := by
  by_cases htwo : 2 ∣ n
  · obtain ⟨r, rfl⟩ := htwo
    rw [if_pos (dvd_mul_right 2 r),
      Nat.mul_div_cancel_left r (by decide : 0 < 2),
      quotientParityDivisorCurrent, ordinaryDivisorCurrent]
    by_cases hr : r = 0
    · subst r
      simp
    have htwoR : 2 * r ≠ 0 := mul_ne_zero (by decide) hr
    have hfibre :
        (2 * r).divisors.filter (fun a => (2 * r / a) % 2 = 0) =
          r.divisors := by
      ext a
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨ha, _⟩, hparity⟩
        have haPos : 0 < a := Nat.pos_of_ne_zero fun hazero => by
          subst a
          apply hr
          simpa using ha
        have hdivmul : 2 * r / a * a = 2 * r := Nat.div_mul_cancel ha
        have heven : 2 ∣ 2 * r / a := Nat.dvd_of_mod_eq_zero hparity
        rcases heven with ⟨q, hq⟩
        refine ⟨?_, hr⟩
        refine ⟨q, ?_⟩
        rw [hq] at hdivmul
        have hcancel : 2 * (q * a) = 2 * r := by
          simpa [mul_assoc] using hdivmul
        have hqa : q * a = r :=
          (Nat.mul_left_cancel (by decide : 0 < 2)) hcancel
        simpa [mul_comm] using hqa.symm
      · rintro ⟨ha, _⟩
        rcases ha with ⟨q, rfl⟩
        have haPos : 0 < a := Nat.pos_of_ne_zero fun hazero => by
          subst a
          simp at hr
        constructor
        · exact ⟨⟨2 * q, by ac_rfl⟩, htwoR⟩
        · rw [show 2 * (a * q) = a * (2 * q) by ac_rfl,
            Nat.mul_div_cancel_left (2 * q) haPos]
          simp
    rw [← Finset.sum_filter, hfibre]
  · rw [if_neg htwo, quotientParityDivisorCurrent]
    apply Finset.sum_eq_zero
    intro a ha
    rw [if_neg]
    intro hparity
    have haDvd : a ∣ n := Nat.dvd_of_mem_divisors ha
    have hdivmul : n / a * a = n := Nat.div_mul_cancel haDvd
    have heven : 2 ∣ n / a := Nat.dvd_of_mod_eq_zero hparity
    exact htwo (dvd_trans heven ⟨a, hdivmul.symm⟩)

/-- The zero-parity current is the coefficient of the exactly dilated
divisor series. -/
theorem quotientParity_zero_eq_dilated_coeff (n : ℕ) :
    quotientParityDivisorCurrent 0 n =
      PowerSeries.coeff n
        (exactDilate 2 (by decide) ordinaryDivisorSeries) := by
  rw [quotientParity_zero_eq_half, coeff_exactDilate]
  simp only [coeff_ordinaryDivisorSeries]

/-- The odd-quotient fibre is the complementary face of the complete
divisor current. -/
theorem quotientParity_one_eq_complement (n : ℕ) :
    quotientParityDivisorCurrent 1 n =
      ordinaryDivisorCurrent n - quotientParityDivisorCurrent 0 n := by
  have h := quotientParity_zero_add_one n
  linarith

/-- At one additive address, same quotient parity is exactly the union of
the even/even and odd/odd factor fibres. -/
theorem sameParityFactorShell (m q : ℕ) :
    (∑ a ∈ m.divisors,
      ∑ b ∈ q.divisors,
        if (m / a) % 2 = (q / b) % 2 then
          (a : ℤ) * (b : ℤ)
        else 0) =
      quotientParityDivisorCurrent 0 m * quotientParityDivisorCurrent 0 q +
        quotientParityDivisorCurrent 1 m * quotientParityDivisorCurrent 1 q := by
  rw [quotientParityDivisorCurrent, quotientParityDivisorCurrent,
    quotientParityDivisorCurrent, quotientParityDivisorCurrent]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have haMod : (m / a) % 2 = 0 ∨ (m / a) % 2 = 1 := by omega
  have hbMod : (q / b) % 2 = 0 ∨ (q / b) % 2 = 1 := by omega
  rcases haMod with haMod | haMod <;>
    rcases hbMod with hbMod | hbMod <;> simp [haMod, hbMod]

/-- The source congruence current is the finite Cauchy sum of its two
quotient-parity fibres. -/
theorem huardPlusCurrent_two_eq_parity_sum (n : ℕ) :
    huardPlusCurrent 2 n =
      ∑ m ∈ Finset.range n,
        (quotientParityDivisorCurrent 0 m *
            quotientParityDivisorCurrent 0 (n - m) +
          quotientParityDivisorCurrent 1 m *
            quotientParityDivisorCurrent 1 (n - m)) := by
  rw [huardPlusCurrent]
  apply Finset.sum_congr rfl
  intro m hm
  exact sameParityFactorShell m (n - m)

/-- The even-quotient/complete mixed current is `W₂(n)`. -/
theorem zeroParity_left_convolution (n : ℕ) :
    (∑ m ∈ Finset.range n,
      quotientParityDivisorCurrent 0 m *
        ordinaryDivisorCurrent (n - m)) =
      doubledDivisorConvolution n := by
  rw [← coeff_exactDilate_two_mul_ordinaryDivisorSeries n,
    PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [coeff_ordinaryDivisorSeries]
  have hend :
      PowerSeries.coeff n (exactDilate 2 (by decide) ordinaryDivisorSeries) *
          ordinaryDivisorCurrent (n - n) = 0 := by
    simp [ordinaryDivisorCurrent]
  rw [hend, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [quotientParity_zero_eq_dilated_coeff]

/-- Swapping the two Cauchy factors returns the same `W₂(n)` current. -/
theorem zeroParity_right_convolution (n : ℕ) :
    (∑ m ∈ Finset.range n,
      ordinaryDivisorCurrent m *
        quotientParityDivisorCurrent 0 (n - m)) =
      doubledDivisorConvolution n := by
  rw [← coeff_exactDilate_two_mul_ordinaryDivisorSeries n]
  conv_rhs =>
    rw [mul_comm]
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [coeff_ordinaryDivisorSeries]
  have hend :
      ordinaryDivisorCurrent n *
          PowerSeries.coeff (n - n)
            (exactDilate 2 (by decide) ordinaryDivisorSeries) = 0 := by
    simp [ordinaryDivisorCurrent, coeff_exactDilate]
  rw [hend, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [quotientParity_zero_eq_dilated_coeff]

/-- Both quotient factors are even exactly when the total address is even;
after halving, their intersection is the ordinary level-one convolution. -/
theorem zeroParity_intersection_convolution (n : ℕ) :
    (∑ m ∈ Finset.range n,
      quotientParityDivisorCurrent 0 m *
        quotientParityDivisorCurrent 0 (n - m)) =
      if 2 ∣ n then ordinaryDivisorConvolution (n / 2) else 0 := by
  have hcoeff :
      PowerSeries.coeff n
          (exactDilate 2 (by decide) ordinaryDivisorSeries *
            exactDilate 2 (by decide) ordinaryDivisorSeries) =
        if 2 ∣ n then ordinaryDivisorConvolution (n / 2) else 0 := by
    rw [← exactDilate_mul, coeff_exactDilate]
    by_cases htwo : 2 ∣ n
    · simp only [if_pos htwo, coeff_ordinaryDivisorSeries_sq]
    · simp only [if_neg htwo]
  rw [← hcoeff, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  have hend :
      PowerSeries.coeff n (exactDilate 2 (by decide) ordinaryDivisorSeries) *
          PowerSeries.coeff (n - n)
            (exactDilate 2 (by decide) ordinaryDivisorSeries) = 0 := by
    simp [coeff_exactDilate, ordinaryDivisorCurrent]
  rw [hend, add_zero]
  apply Finset.sum_congr rfl
  intro m hm
  rw [quotientParity_zero_eq_dilated_coeff,
    quotientParity_zero_eq_dilated_coeff]

/-- The same-parity current decomposes into the full current, the two
scale-two faces, and their exactly retained intersection. -/
theorem huardPlusCurrent_two_expansion (n : ℕ) :
    huardPlusCurrent 2 n =
      ordinaryDivisorConvolution n -
        doubledDivisorConvolution n -
        doubledDivisorConvolution n +
        2 * (if 2 ∣ n then ordinaryDivisorConvolution (n / 2) else 0) := by
  rw [huardPlusCurrent_two_eq_parity_sum]
  have hpoint (m : ℕ) :
      quotientParityDivisorCurrent 0 m *
            quotientParityDivisorCurrent 0 (n - m) +
          quotientParityDivisorCurrent 1 m *
            quotientParityDivisorCurrent 1 (n - m) =
        ordinaryDivisorCurrent m * ordinaryDivisorCurrent (n - m) -
          ordinaryDivisorCurrent m * quotientParityDivisorCurrent 0 (n - m) -
          quotientParityDivisorCurrent 0 m * ordinaryDivisorCurrent (n - m) +
          2 * (quotientParityDivisorCurrent 0 m *
            quotientParityDivisorCurrent 0 (n - m)) := by
    rw [quotientParity_one_eq_complement,
      quotientParity_one_eq_complement]
    ring
  apply Eq.trans (Finset.sum_congr rfl fun m hm => hpoint m)
  calc
    _ =
        (∑ m ∈ Finset.range n,
            ordinaryDivisorCurrent m * ordinaryDivisorCurrent (n - m)) -
          (∑ m ∈ Finset.range n,
            ordinaryDivisorCurrent m *
              quotientParityDivisorCurrent 0 (n - m)) -
          (∑ m ∈ Finset.range n,
            quotientParityDivisorCurrent 0 m *
              ordinaryDivisorCurrent (n - m)) +
          2 * (∑ m ∈ Finset.range n,
            quotientParityDivisorCurrent 0 m *
              quotientParityDivisorCurrent 0 (n - m)) := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
    _ = _ := by
      rw [ordinaryDivisorConvolution,
        zeroParity_right_convolution,
        zeroParity_left_convolution,
        zeroParity_intersection_convolution]

/-- **HUARD PARITY RETURN.**  The exact factor fibres inhabit the parity
reindexing proposition used by the source reduction. -/
theorem huardParityReindexing : HuardParityReindexing := by
  intro n
  rw [huardPlusCurrent_two_expansion]
  by_cases htwo : 2 ∣ n
  · simp only [if_pos htwo]
    ring
  · simp only [if_neg htwo]
    ring

#print axioms quotientParity_zero_eq_half
#print axioms sameParityFactorShell
#print axioms huardParityReindexing

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardParityReindexing
