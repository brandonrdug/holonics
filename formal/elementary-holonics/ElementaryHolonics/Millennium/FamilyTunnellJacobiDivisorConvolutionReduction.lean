import ElementaryHolonics.Millennium.FamilyTunnellJacobiCompletedEulerConnection
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Conditional reduction of the Jacobi divisor recurrence

This file isolates the sole external arithmetic input in the differentiated
Jacobi four-square passage: the classical level-two additive convolution law
for the first divisor current.  Everything after that hypothesis is finite
divisor partitioning, exact reindexing, and integer algebra.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction

open Finset PowerSeries
open Soma.Holonics.Mathematics.PowerSeriesExactDilation
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareEulerReturn
open Soma.Holonics.Millennium.FamilyTunnellJacobiFiniteEulerConnection
open Soma.Holonics.Millennium.FamilyTunnellJacobiCompletedEulerConnection
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct

/-- Sum of the cubes of all positive divisors. -/
def cubicDivisorCurrent (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) ^ 3

/-- Level-one additive (Cauchy) convolution of ordinary divisor currents. -/
def ordinaryDivisorConvolution (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n,
    ordinaryDivisorCurrent k * ordinaryDivisorCurrent (n - k)

/-- Level-two additive convolution `W₂(n)`.  Truncated subtraction creates
no spurious current because the divisor current at address zero is zero. -/
def doubledDivisorConvolution (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n,
    ordinaryDivisorCurrent k * ordinaryDivisorCurrent (n - 2 * k)

/-- The one source-specific arithmetic input.  It is an explicit hypothesis,
not a repository axiom. -/
def DoubledDivisorConvolutionFormula : Prop :=
  ∀ n : ℕ,
    24 * doubledDivisorConvolution n =
      2 * cubicDivisorCurrent n +
        (1 - 3 * (n : ℤ)) * ordinaryDivisorCurrent n +
        if 2 ∣ n then
          8 * cubicDivisorCurrent (n / 2) +
            (1 - 6 * (n : ℤ)) * ordinaryDivisorCurrent (n / 2)
        else 0

/-- The ordinary divisor current as an exact formal series. -/
def ordinaryDivisorSeries : PowerSeries ℤ :=
  PowerSeries.mk ordinaryDivisorCurrent

@[simp] theorem coeff_ordinaryDivisorSeries (n : ℕ) :
    PowerSeries.coeff n ordinaryDivisorSeries = ordinaryDivisorCurrent n := by
  simp [ordinaryDivisorSeries]

@[simp] theorem coeff_ordinaryDivisorSeries_zero :
    PowerSeries.coeff 0 ordinaryDivisorSeries = 0 := by
  simp [ordinaryDivisorCurrent]

/-- The level-one finite convolution is the corresponding Cauchy
coefficient. -/
theorem coeff_ordinaryDivisorSeries_sq (n : ℕ) :
    PowerSeries.coeff n (ordinaryDivisorSeries * ordinaryDivisorSeries) =
      ordinaryDivisorConvolution n := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, ordinaryDivisorConvolution]
  simp [ordinaryDivisorCurrent]

/-- The level-two finite convolution is the Cauchy coefficient of the
scale-two divisor stream against the undilated stream. -/
theorem coeff_exactDilate_two_mul_ordinaryDivisorSeries (n : ℕ) :
    PowerSeries.coeff n
        (exactDilate 2 (by decide) ordinaryDivisorSeries *
          ordinaryDivisorSeries) =
      doubledDivisorConvolution n := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [coeff_exactDilate, coeff_ordinaryDivisorSeries]
  have hend :
      (if 2 ∣ n then ordinaryDivisorCurrent (n / 2) else 0) *
          ordinaryDivisorCurrent (n - n) = 0 := by
    simp [ordinaryDivisorCurrent]
  rw [hend, add_zero]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hleft :
      (∑ k ∈ (Finset.range n).filter (fun k => 2 ∣ k),
          ordinaryDivisorCurrent (k / 2) * ordinaryDivisorCurrent (n - k)) =
        ∑ k ∈ (Finset.range n).filter (fun k => 0 < k ∧ 2 ∣ k),
          ordinaryDivisorCurrent (k / 2) * ordinaryDivisorCurrent (n - k) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨hk.1, hk.2.2⟩
    · intro k hk hnot
      rw [Finset.mem_filter] at hk
      have hkzero : k = 0 := by
        by_contra hkne
        apply hnot
        rw [Finset.mem_filter]
        exact ⟨hk.1, Nat.pos_of_ne_zero hkne, hk.2⟩
      subst k
      simp [ordinaryDivisorCurrent]
  rw [hleft]
  have hright :
      doubledDivisorConvolution n =
        ∑ r ∈ (Finset.range n).filter (fun r => 0 < r ∧ 2 * r < n),
          ordinaryDivisorCurrent r * ordinaryDivisorCurrent (n - 2 * r) := by
    rw [doubledDivisorConvolution, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrpos : 0 < r
    · by_cases hlt : 2 * r < n
      · simp [hrpos, hlt]
      · have hz : n - 2 * r = 0 := by omega
        simp [hrpos, hlt, hz, ordinaryDivisorCurrent]
    · have hrzero : r = 0 := by omega
      subst r
      simp [ordinaryDivisorCurrent]
  rw [hright]
  apply Finset.sum_bij (fun k hk => k / 2)
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    have hkn : k < n := Finset.mem_range.mp hk.1
    rcases hk.2.2 with ⟨r, hr⟩
    constructor
    · rw [Finset.mem_range]
      omega
    · constructor <;> omega
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    rcases ha.2.2 with ⟨ra, hra⟩
    rcases hb.2.2 with ⟨rb, hrb⟩
    omega
  · intro r hr
    rw [Finset.mem_filter] at hr
    refine ⟨2 * r, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · exact ⟨by omega, dvd_mul_right 2 r⟩
    · omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk.2.2 with ⟨r, hr⟩
    have hhalf : k / 2 = r := by omega
    rw [hhalf, show k = 2 * r by omega]

/-- The source population of `W₂(n)` contains exactly the positive addresses
`r` whose doubled address lies strictly below `n`.  This public form is the
finite carrier used by the Huard parity reindexing. -/
theorem doubledDivisorConvolution_eq_positive (n : ℕ) :
    doubledDivisorConvolution n =
      ∑ r ∈ (Finset.range n).filter (fun r => 0 < r ∧ 2 * r < n),
        ordinaryDivisorCurrent r * ordinaryDivisorCurrent (n - 2 * r) := by
  rw [doubledDivisorConvolution, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hrpos : 0 < r
  · by_cases hlt : 2 * r < n
    · simp [hrpos, hlt]
    · have hz : n - 2 * r = 0 := by omega
      simp [hrpos, hlt, hz, ordinaryDivisorCurrent]
  · have hrzero : r = 0 := by omega
    subst r
    simp [ordinaryDivisorCurrent]

/-- Two successive binary dilations retain exactly the scale-four chart. -/
private theorem exactDilate_two_comp (F : PowerSeries ℤ) :
    exactDilate 2 (by decide) (exactDilate 2 (by decide) F) =
      exactDilate 4 (by decide) F := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_exactDilate]
  by_cases hfour : 4 ∣ n
  · rcases hfour with ⟨r, rfl⟩
    have hfirst : 2 ∣ 4 * r := ⟨2 * r, by omega⟩
    have hsecond : 2 ∣ 4 * r / 2 := by
      refine ⟨r, ?_⟩
      omega
    rw [if_pos hfirst, if_pos hsecond]
    rw [show 4 * r / 2 / 2 = r by omega,
      show 4 * r / 4 = r by omega]
    rw [if_pos (dvd_mul_right 4 r)]
  · by_cases htwo : 2 ∣ n
    · rw [if_pos htwo, if_neg hfour]
      have hnotHalf : ¬ 2 ∣ n / 2 := by
        intro hh
        rcases htwo with ⟨r, rfl⟩
        simp only [Nat.mul_div_cancel_left r (by decide : 0 < 2)] at hh
        rcases hh with ⟨s, rfl⟩
        exact hfour ⟨s, by omega⟩
      rw [if_neg hnotHalf]
    · rw [if_neg htwo, if_neg hfour]

/-- The two scaled mixed product has exactly the rebased `W₂` coefficient. -/
private theorem coeff_scaleTwo_mul_scaleFour (n : ℕ) :
    PowerSeries.coeff n
        (exactDilate 2 (by decide) ordinaryDivisorSeries *
          exactDilate 4 (by decide) ordinaryDivisorSeries) =
      if 2 ∣ n then doubledDivisorConvolution (n / 2) else 0 := by
  have hbody :
      exactDilate 2 (by decide) ordinaryDivisorSeries *
          exactDilate 4 (by decide) ordinaryDivisorSeries =
        exactDilate 2 (by decide)
          (ordinaryDivisorSeries *
            exactDilate 2 (by decide) ordinaryDivisorSeries) := by
    rw [exactDilate_mul, exactDilate_two_comp]
  rw [hbody, coeff_exactDilate]
  by_cases htwo : 2 ∣ n
  · rw [if_pos htwo]
    rw [mul_comm, coeff_exactDilate_two_mul_ordinaryDivisorSeries]
    simp [htwo]
  · rw [if_neg htwo]
    simp [htwo]

/-- The scale-four square has the rebased level-one coefficient. -/
private theorem coeff_scaleFour_sq (n : ℕ) :
    PowerSeries.coeff n
        (exactDilate 4 (by decide) ordinaryDivisorSeries *
          exactDilate 4 (by decide) ordinaryDivisorSeries) =
      if 4 ∣ n then ordinaryDivisorConvolution (n / 4) else 0 := by
  rw [← exactDilate_mul, coeff_exactDilate]
  by_cases hfour : 4 ∣ n
  · rw [if_pos hfour, coeff_ordinaryDivisorSeries_sq]
    simp [hfour]
  · rw [if_neg hfour]
    simp [hfour]

/-- Coefficient-valued form of the quartic connection. -/
private def thetaConnectionCoeffSeries : PowerSeries ℤ :=
  PowerSeries.mk thetaQuarticConnectionCoeff

/-- Coefficient-valued form of the Jacobi divisor current. -/
private def jacobiDivisorSeries : PowerSeries ℤ :=
  PowerSeries.mk jacobiDivisorCurrent

@[simp] private theorem coeff_thetaConnectionCoeffSeries (n : ℕ) :
    PowerSeries.coeff n thetaConnectionCoeffSeries =
      thetaQuarticConnectionCoeff n := by
  simp [thetaConnectionCoeffSeries]

@[simp] private theorem coeff_jacobiDivisorSeries (n : ℕ) :
    PowerSeries.coeff n jacobiDivisorSeries = jacobiDivisorCurrent n := by
  simp [jacobiDivisorSeries]

private theorem thetaConnectionCoeffSeries_eq :
    thetaConnectionCoeffSeries =
      ordinaryDivisorSeries -
        PowerSeries.C (5 : ℤ) * exactDilate 2 (by decide) ordinaryDivisorSeries +
        PowerSeries.C (4 : ℤ) * exactDilate 4 (by decide) ordinaryDivisorSeries := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_thetaConnectionCoeffSeries, map_add, map_sub,
    PowerSeries.coeff_C_mul,
    coeff_ordinaryDivisorSeries, coeff_exactDilate]
  simp [thetaQuarticConnectionCoeff]

private theorem jacobiDivisorSeries_eq :
    jacobiDivisorSeries =
      ordinaryDivisorSeries -
        PowerSeries.C (4 : ℤ) * exactDilate 4 (by decide) ordinaryDivisorSeries := by
  apply PowerSeries.ext
  intro n
  simp only [coeff_jacobiDivisorSeries, map_sub, PowerSeries.coeff_C_mul,
    coeff_ordinaryDivisorSeries, coeff_exactDilate]
  simp [jacobiDivisorCurrent_eq_sigma_difference]

/-- Ring expansion of the level-four connection/divisor interaction. -/
private theorem thetaConnection_mul_jacobiDivisorSeries_eq :
    thetaConnectionCoeffSeries * jacobiDivisorSeries =
      ordinaryDivisorSeries * ordinaryDivisorSeries -
        PowerSeries.C (5 : ℤ) *
          (exactDilate 2 (by decide) ordinaryDivisorSeries *
            ordinaryDivisorSeries) +
        PowerSeries.C (5 : ℤ) *
          (PowerSeries.C (4 : ℤ) *
            (exactDilate 2 (by decide) ordinaryDivisorSeries *
              exactDilate 4 (by decide) ordinaryDivisorSeries)) -
        PowerSeries.C (4 : ℤ) *
          (PowerSeries.C (4 : ℤ) *
            (exactDilate 4 (by decide) ordinaryDivisorSeries *
              exactDilate 4 (by decide) ordinaryDivisorSeries)) := by
  rw [thetaConnectionCoeffSeries_eq, jacobiDivisorSeries_eq]
  ring

/-- Exact finite convolution returned by the level-four interaction. -/
theorem coeff_thetaConnection_mul_jacobiDivisorSeries (n : ℕ) :
    PowerSeries.coeff n
        (thetaConnectionCoeffSeries * jacobiDivisorSeries) =
      ordinaryDivisorConvolution n - 5 * doubledDivisorConvolution n +
        (if 2 ∣ n then 20 * doubledDivisorConvolution (n / 2) else 0) -
        (if 4 ∣ n then 16 * ordinaryDivisorConvolution (n / 4) else 0) := by
  rw [thetaConnection_mul_jacobiDivisorSeries_eq]
  simp only [map_sub, map_add, PowerSeries.coeff_C_mul,
    coeff_ordinaryDivisorSeries_sq,
    coeff_exactDilate_two_mul_ordinaryDivisorSeries,
    coeff_scaleTwo_mul_scaleFour, coeff_scaleFour_sq]
  by_cases hfour : 4 ∣ n
  · have htwo : 2 ∣ n := dvd_trans (by decide : 2 ∣ 4) hfour
    simp [htwo, hfour]
    ring
  · by_cases htwo : 2 ∣ n
    · simp [htwo, hfour]
      ring
    · simp [htwo, hfour]

/-- The Cauchy coefficient is exactly the strictly descending sum used by
`JacobiDivisorConnectionRecurrence`. -/
theorem coeff_thetaConnection_mul_jacobi_succ (m : ℕ) :
    PowerSeries.coeff (m + 1)
        (thetaConnectionCoeffSeries * jacobiDivisorSeries) =
      ∑ j ∈ Finset.range m,
        thetaQuarticConnectionCoeff (j + 1) *
          jacobiDivisorCurrent (m - j) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ]
  simp only [coeff_thetaConnectionCoeffSeries, coeff_jacobiDivisorSeries]
  have hend :
      thetaQuarticConnectionCoeff (m + 1) * jacobiDivisorCurrent 0 = 0 := by
    simp [jacobiDivisorCurrent, nonFourDivisors]
  simp only [Nat.sub_self]
  rw [hend, add_zero, Finset.sum_range_succ']
  simp only [thetaQuarticConnectionCoeff_zero, zero_mul,
    Nat.add_sub_add_right]
  simp

/-- The power-`p` divisor current used only to prove exact doubling. -/
private def divisorPowerCurrent (p n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, (d : ℤ) ^ p

/-- The even-address fibre inside a power-divisor current. -/
private def evenDivisorPowerCurrent (p n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors.filter fun d => 2 ∣ d, (d : ℤ) ^ p

private def timesTwoEmbedding : ℕ ↪ ℕ where
  toFun d := 2 * d
  inj' := by
    intro a b h
    exact mul_left_cancel₀ (by decide : (2 : ℕ) ≠ 0) h

/-- Multiplication by two identifies the complete divisor population of `m`
with the even divisor fibre of `2m`. -/
private theorem evenDivisorPowerCurrent_two_mul (p m : ℕ) :
    evenDivisorPowerCurrent p (2 * m) =
      (2 : ℤ) ^ p * divisorPowerCurrent p m := by
  by_cases hm : m = 0
  · subst m
    simp [evenDivisorPowerCurrent, divisorPowerCurrent]
  have htwoM : 2 * m ≠ 0 := mul_ne_zero (by decide) hm
  have hfibre :
      (2 * m).divisors.filter (fun d => 2 ∣ d) =
        m.divisors.map timesTwoEmbedding := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
    constructor
    · rintro ⟨⟨hdvd, _⟩, htwo⟩
      rcases htwo with ⟨e, rfl⟩
      refine ⟨e, ⟨?_, hm⟩, rfl⟩
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp hdvd
    · rintro ⟨e, ⟨he, _⟩, rfl⟩
      refine ⟨⟨?_, htwoM⟩, dvd_mul_right 2 e⟩
      exact mul_dvd_mul_left 2 he
  rw [evenDivisorPowerCurrent, hfibre, divisorPowerCurrent]
  simp only [Finset.sum_map, timesTwoEmbedding]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _hd
  change (((2 * d : ℕ) : ℤ) ^ p) = (2 : ℤ) ^ p * (d : ℤ) ^ p
  push_cast
  exact mul_pow _ _ _

/-- The odd divisor fibres of `m` and `2m` coincide. -/
private theorem oddDivisorPowerCurrent_two_mul (p m : ℕ) :
    (∑ d ∈ (2 * m).divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ p) =
      ∑ d ∈ m.divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ p := by
  by_cases hm : m = 0
  · subst m
    simp
  have htwoM : 2 * m ≠ 0 := mul_ne_zero (by decide) hm
  congr 1
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, _⟩, hodd⟩
    have hcop : d.Coprime 2 :=
      (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).symm
    exact ⟨⟨(hcop.dvd_mul_left).mp (by simpa [mul_comm] using hd), hm⟩, hodd⟩
  · rintro ⟨⟨hd, _⟩, hodd⟩
    exact ⟨⟨dvd_mul_of_dvd_right hd 2, htwoM⟩, hodd⟩

/-- Exact two-adic doubling of every power-divisor current. -/
private theorem divisorPowerCurrent_two_mul (p n : ℕ) :
    divisorPowerCurrent p (2 * n) =
      (1 + (2 : ℤ) ^ p) * divisorPowerCurrent p n -
        if 2 ∣ n then
          (2 : ℤ) ^ p * divisorPowerCurrent p (n / 2)
        else 0 := by
  have hsplit (r : ℕ) :
      divisorPowerCurrent p r =
        evenDivisorPowerCurrent p r +
          ∑ d ∈ r.divisors.filter (fun d => ¬ 2 ∣ d), (d : ℤ) ^ p := by
    rw [divisorPowerCurrent, evenDivisorPowerCurrent]
    have h := Finset.sum_filter_add_sum_filter_not r.divisors
      (fun d => 2 ∣ d) (fun d => (d : ℤ) ^ p)
    linarith
  rw [hsplit (2 * n), evenDivisorPowerCurrent_two_mul,
    oddDivisorPowerCurrent_two_mul, hsplit n]
  by_cases htwo : 2 ∣ n
  · obtain ⟨m, rfl⟩ := htwo
    rw [if_pos (dvd_mul_right 2 m), Nat.mul_div_cancel_left m (by decide : 0 < 2),
      evenDivisorPowerCurrent_two_mul]
    ring
  · rw [if_neg htwo]
    have hevenZero : evenDivisorPowerCurrent p n = 0 := by
      unfold evenDivisorPowerCurrent
      apply Finset.sum_eq_zero
      intro d hd
      exact (htwo (dvd_trans (Finset.mem_filter.mp hd).2
        (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1))).elim
    rw [hevenZero]
    ring

private theorem divisorPowerCurrent_one (n : ℕ) :
    divisorPowerCurrent 1 n = ordinaryDivisorCurrent n := by
  simp [divisorPowerCurrent, ordinaryDivisorCurrent]

private theorem divisorPowerCurrent_three (n : ℕ) :
    divisorPowerCurrent 3 n = cubicDivisorCurrent n := by
  rfl

/-- First-divisor current under an exact doubling. -/
theorem ordinaryDivisorCurrent_two_mul (n : ℕ) :
    ordinaryDivisorCurrent (2 * n) =
      3 * ordinaryDivisorCurrent n -
        if 2 ∣ n then 2 * ordinaryDivisorCurrent (n / 2) else 0 := by
  simpa [divisorPowerCurrent_one] using divisorPowerCurrent_two_mul 1 n

/-- Cubic-divisor current under an exact doubling. -/
theorem cubicDivisorCurrent_two_mul (n : ℕ) :
    cubicDivisorCurrent (2 * n) =
      9 * cubicDivisorCurrent n -
        if 2 ∣ n then 8 * cubicDivisorCurrent (n / 2) else 0 := by
  simpa [divisorPowerCurrent_three] using divisorPowerCurrent_two_mul 3 n

private def complementaryDoubledDivisorConvolution (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n,
    if 2 ∣ n - k then
      ordinaryDivisorCurrent k * ordinaryDivisorCurrent ((n - k) / 2)
    else 0

/-- Swapping the two addressed summands carries the complementary level-two
convolution back to `W₂`. -/
private theorem complementaryDoubledDivisorConvolution_eq (n : ℕ) :
    complementaryDoubledDivisorConvolution n = doubledDivisorConvolution n := by
  have hleft :
      complementaryDoubledDivisorConvolution n =
        ∑ k ∈ (Finset.range n).filter
            (fun k => 0 < k ∧ 2 ∣ n - k),
          ordinaryDivisorCurrent k * ordinaryDivisorCurrent ((n - k) / 2) := by
    rw [complementaryDoubledDivisorConvolution, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkpos : 0 < k
    · by_cases htwo : 2 ∣ n - k
      · simp [hkpos, htwo]
      · simp [hkpos, htwo]
    · have hkzero : k = 0 := by omega
      subst k
      simp [ordinaryDivisorCurrent]
  have hright :
      doubledDivisorConvolution n =
        ∑ r ∈ (Finset.range n).filter (fun r => 0 < r ∧ 2 * r < n),
          ordinaryDivisorCurrent r * ordinaryDivisorCurrent (n - 2 * r) := by
    rw [doubledDivisorConvolution, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hrpos : 0 < r
    · by_cases hlt : 2 * r < n
      · simp [hrpos, hlt]
      · have hz : n - 2 * r = 0 := by omega
        simp [hrpos, hlt, hz, ordinaryDivisorCurrent]
    · have hrzero : r = 0 := by omega
      subst r
      simp [ordinaryDivisorCurrent]
  rw [hleft, hright]
  apply Finset.sum_bij (fun k hk => (n - k) / 2)
  · intro k hk
    rw [Finset.mem_filter] at hk ⊢
    have hkn : k < n := Finset.mem_range.mp hk.1
    rcases hk.2.2 with ⟨r, hr⟩
    constructor
    · rw [Finset.mem_range]
      omega
    · constructor <;> omega
  · intro a ha b hb hab
    rw [Finset.mem_filter] at ha hb
    rcases ha.2.2 with ⟨ra, hra⟩
    rcases hb.2.2 with ⟨rb, hrb⟩
    have han : a < n := Finset.mem_range.mp ha.1
    have hbn : b < n := Finset.mem_range.mp hb.1
    omega
  · intro r hr
    rw [Finset.mem_filter] at hr
    refine ⟨n - 2 * r, ?_, ?_⟩
    · rw [Finset.mem_filter]
      constructor
      · rw [Finset.mem_range]
        omega
      · constructor
        · omega
        · refine ⟨r, ?_⟩
          omega
    · omega
  · intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk.2.2 with ⟨r, hr⟩
    have hkn : k < n := Finset.mem_range.mp hk.1
    have hhalf : (n - k) / 2 = r := by omega
    rw [hhalf]
    rw [show k = n - 2 * r by omega]
    ring

/-- Even evaluation of `W₂` returns three level-one copies minus the
swapped level-two copy. -/
theorem doubledConvolution_two_mul (n : ℕ) :
    doubledDivisorConvolution (2 * n) +
        2 * doubledDivisorConvolution n =
      3 * ordinaryDivisorConvolution n := by
  rw [doubledDivisorConvolution, show 2 * n = n + n by omega,
    Finset.sum_range_add]
  have htail :
      (∑ k ∈ Finset.range n,
        ordinaryDivisorCurrent (n + k) *
          ordinaryDivisorCurrent (n + n - 2 * (n + k))) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have hz : n + n - 2 * (n + k) = 0 := by omega
    simp [hz, ordinaryDivisorCurrent]
  rw [htail, add_zero]
  have hhead :
      (∑ k ∈ Finset.range n,
        ordinaryDivisorCurrent k *
          ordinaryDivisorCurrent (n + n - 2 * k)) =
        3 * ordinaryDivisorConvolution n -
          2 * complementaryDoubledDivisorConvolution n := by
    rw [ordinaryDivisorConvolution, complementaryDoubledDivisorConvolution,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < n := Finset.mem_range.mp hk
    have harg : n + n - 2 * k = 2 * (n - k) := by omega
    rw [harg, ordinaryDivisorCurrent_two_mul]
    by_cases htwo : 2 ∣ n - k
    · rw [if_pos htwo, if_pos htwo]
      ring
    · rw [if_neg htwo, if_neg htwo]
      ring
  rw [hhead, complementaryDoubledDivisorConvolution_eq]
  ring

/-- The level-one Besge convolution law is not a second input: it is returned
by the level-two law at `n` and `2n` together with exact divisor doubling. -/
theorem ordinaryDivisorConvolution_formula_of_doubled
    (hformula : DoubledDivisorConvolutionFormula) (n : ℕ) :
    12 * ordinaryDivisorConvolution n =
      5 * cubicDivisorCurrent n +
        (1 - 6 * (n : ℤ)) * ordinaryDivisorCurrent n := by
  have hrelation := doubledConvolution_two_mul n
  have hn := hformula n
  have htwoN := hformula (2 * n)
  have hdiv : 2 ∣ 2 * n := dvd_mul_right 2 n
  rw [if_pos hdiv, Nat.mul_div_cancel_left n (by decide : 0 < 2),
    cubicDivisorCurrent_two_mul, ordinaryDivisorCurrent_two_mul] at htwoN
  by_cases htwo : 2 ∣ n
  · rw [if_pos htwo] at hn htwoN
    push_cast at htwoN
    simp [htwo] at htwoN
    ring_nf at hn htwoN hrelation ⊢
    linarith
  · rw [if_neg htwo] at hn htwoN
    push_cast at htwoN
    simp [htwo] at htwoN
    ring_nf at hn htwoN hrelation ⊢
    linarith

/-- The level-two formula returns the exact level-four convolution current.
All cubic divisor faces cancel. -/
theorem eight_coeff_thetaConnection_mul_jacobi_of_doubled
    (hformula : DoubledDivisorConvolutionFormula) (n : ℕ) :
    8 * PowerSeries.coeff n
        (thetaConnectionCoeffSeries * jacobiDivisorSeries) =
      ((n : ℤ) - 1) * ordinaryDivisorCurrent n +
        (if 2 ∣ n then 5 * ordinaryDivisorCurrent (n / 2) else 0) -
        (if 4 ∣ n then
          4 * ((n : ℤ) + 1) * ordinaryDivisorCurrent (n / 4)
        else 0) := by
  rw [coeff_thetaConnection_mul_jacobiDivisorSeries]
  have hwOne := ordinaryDivisorConvolution_formula_of_doubled hformula n
  have hwTwo := hformula n
  by_cases htwo : 2 ∣ n
  · rcases htwo with ⟨r, rfl⟩
    have htwoFull : 2 ∣ 2 * r := dvd_mul_right 2 r
    by_cases htwoR : 2 ∣ r
    · rcases htwoR with ⟨s, rfl⟩
      have hfourFull : 4 ∣ 2 * (2 * s) := by
        refine ⟨s, by omega⟩
      have htwoHalf : 2 ∣ 2 * s := dvd_mul_right 2 s
      have hwTwoHalf := hformula (2 * s)
      have hwOneQuarter :=
        ordinaryDivisorConvolution_formula_of_doubled hformula s
      rw [if_pos htwoFull, if_pos hfourFull,
        Nat.mul_div_cancel_left (2 * s) (by decide : 0 < 2),
        show 2 * (2 * s) / 4 = s by omega]
      rw [if_pos htwoFull,
        Nat.mul_div_cancel_left (2 * s) (by decide : 0 < 2)] at hwTwo
      rw [if_pos htwoHalf,
        Nat.mul_div_cancel_left s (by decide : 0 < 2)] at hwTwoHalf
      push_cast at hwOne hwTwo hwTwoHalf
      ring_nf at hwOne hwTwo hwTwoHalf hwOneQuarter
      ring_nf
      have htwoNorm : 2 ∣ s * 4 := ⟨2 * s, by omega⟩
      have hfourNorm : 4 ∣ s * 4 := ⟨s, by omega⟩
      simp only [if_pos htwoNorm, if_pos hfourNorm]
      norm_num [Nat.mul_div_cancel_left]
      ring_nf
      linarith
    · have hfourFull : ¬ 4 ∣ 2 * r := by
        rintro ⟨s, hs⟩
        apply htwoR
        refine ⟨s, ?_⟩
        omega
      have hwTwoHalf := hformula r
      rw [if_pos htwoFull, if_neg hfourFull,
        Nat.mul_div_cancel_left r (by decide : 0 < 2)]
      rw [if_pos htwoFull,
        Nat.mul_div_cancel_left r (by decide : 0 < 2)] at hwTwo
      rw [if_neg htwoR] at hwTwoHalf
      push_cast at hwOne hwTwo
      ring_nf at hwOne hwTwo hwTwoHalf
      ring_nf
      have htwoNorm : 2 ∣ r * 2 := ⟨r, by omega⟩
      have hfourNorm : ¬ 4 ∣ r * 2 := by
        simpa [mul_comm] using hfourFull
      simp only [if_pos htwoNorm, if_neg hfourNorm]
      norm_num [Nat.mul_div_cancel_left]
      ring_nf
      linarith
  · have hfour : ¬ 4 ∣ n := fun h =>
      htwo (dvd_trans (by decide : 2 ∣ 4) h)
    simp only [if_neg htwo, if_neg hfour]
    rw [if_neg htwo] at hwTwo
    ring_nf at hwOne hwTwo ⊢
    linarith

/-- **CONDITIONAL JACOBI DIVISOR RECURRENCE.**  The single classical
level-two convolution formula entails the exact strictly descending
connection law used by the completed Lambert receiver. -/
theorem jacobiDivisorConnectionRecurrence_of_doubled
    (hformula : DoubledDivisorConvolutionFormula) :
    JacobiDivisorConnectionRecurrence := by
  intro m
  have hconv :=
    eight_coeff_thetaConnection_mul_jacobi_of_doubled hformula (m + 1)
  rw [coeff_thetaConnection_mul_jacobi_succ] at hconv
  rw [jacobiDivisorCurrent_eq_sigma_difference,
    thetaQuarticConnectionCoeff]
  by_cases hfour : 4 ∣ m + 1
  · have htwo : 2 ∣ m + 1 :=
      dvd_trans (by decide : 2 ∣ 4) hfour
    simp only [if_pos htwo, if_pos hfour] at hconv ⊢
    ring_nf at hconv ⊢
    linarith
  · by_cases htwo : 2 ∣ m + 1
    · simp only [if_pos htwo, if_neg hfour] at hconv ⊢
      ring_nf at hconv ⊢
      linarith
    · simp only [if_neg htwo, if_neg hfour] at hconv ⊢
      ring_nf at hconv ⊢
      linarith

/-- The conditional recurrence and the checked theta-product law reconstruct
the complete Jacobi source/receiver identity. -/
theorem fullFourSquareTheta_eq_completedLambert_of_doubled
    (hformula : DoubledDivisorConvolutionFormula) :
    fullFourSquareTheta = completedJacobiFourSquareLambertSeries := by
  apply fullFourSquareTheta_eq_completedLambert_of_commonEulerConnection
  · simpa [HasEulerConnection] using hasEulerConnection_fullFourSquareTheta
  · exact jacobiDivisorConnectionRecurrence_of_doubled hformula

/-- The same single arithmetic input closes every positive four-square
shell/divisor receiver, not only a finite coefficient aperture. -/
theorem totalShellDivisorLaw_of_doubled
    (hformula : DoubledDivisorConvolutionFormula) :
    ∀ n : ℕ, 0 < n →
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  apply totalShellDivisorLaw_of_commonEulerConnection
  · simpa [HasEulerConnection] using hasEulerConnection_fullFourSquareTheta
  · exact jacobiDivisorConnectionRecurrence_of_doubled hformula

#print axioms ordinaryDivisorCurrent_two_mul
#print axioms cubicDivisorCurrent_two_mul
#print axioms doubledConvolution_two_mul
#print axioms ordinaryDivisorConvolution_formula_of_doubled
#print axioms eight_coeff_thetaConnection_mul_jacobi_of_doubled
#print axioms jacobiDivisorConnectionRecurrence_of_doubled
#print axioms fullFourSquareTheta_eq_completedLambert_of_doubled
#print axioms totalShellDivisorLaw_of_doubled

end Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
