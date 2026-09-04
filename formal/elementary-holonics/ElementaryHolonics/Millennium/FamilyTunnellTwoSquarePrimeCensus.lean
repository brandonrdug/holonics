import ElementaryHolonics.Millennium.FamilyTunnellFourSquarePrimeCensus
import ElementaryHolonics.Millennium.GaussCoefficient
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Exact two-square prime census for the imprimitive Hopf boundary

The two imprimitive endpoints of the Hopf return are populated by Gaussian
norm-`p` sources.  This file constructs and counts that finite source rather
than replacing it by the phrase "sum of two squares".  At a prime congruent to
one modulo four, Fermat existence plus the already proved uniqueness theorem
returns one eight-point signed/permuted orbit.  At a prime congruent to three
modulo four, the carrier is empty.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellTwoSquarePrimeCensus

open Finset
open Soma.Holonics.Millennium.GaussCoefficient

/-- The complete ordered integral two-square shell. -/
def twoSquarePrimePopulation (p : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(p : ℤ)) (p : ℤ)) ×ˢ
      Finset.Icc (-(p : ℤ)) (p : ℤ)).filter fun q =>
    q.1 ^ 2 + q.2 ^ 2 = (p : ℤ)

private theorem coordinate_mem_prime_box {p : ℕ} (hp : 0 < p)
    {a b : ℤ} (hab : a ^ 2 + b ^ 2 = (p : ℤ)) :
    a ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) := by
  rw [Finset.mem_Icc]
  have hpZ : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  constructor <;>
    nlinarith [sq_nonneg a, sq_nonneg b,
      sq_nonneg (a + (p : ℤ)), sq_nonneg (a - (p : ℤ))]

theorem mem_twoSquarePrimePopulation_iff {p : ℕ} (hp : 0 < p)
    (q : ℤ × ℤ) :
    q ∈ twoSquarePrimePopulation p ↔
      q.1 ^ 2 + q.2 ^ 2 = (p : ℤ) := by
  rw [twoSquarePrimePopulation, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_product.mpr ⟨coordinate_mem_prime_box hp h,
      coordinate_mem_prime_box hp (by simpa [add_comm] using h)⟩, h⟩

/-- The two orientations of one nonzero coordinate. -/
def signOrbit (a : ℤ) : Finset ℤ := {a, -a}

/-- All independent signs and the coordinate swap of a normalized Gaussian
prime factor. -/
def signedPermutationOrbit (A B : ℤ) : Finset (ℤ × ℤ) :=
  (signOrbit A ×ˢ signOrbit B) ∪ (signOrbit B ×ˢ signOrbit A)

private theorem sq_eq_sq_cases {u a : ℤ} (h : u ^ 2 = a ^ 2) :
    u = a ∨ u = -a := by
  have hfactor : (u - a) * (u + a) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hzero | hzero
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Prime two-square uniqueness opens the complete shell into its explicit
signed/permuted orbit. -/
theorem twoSquarePrimePopulation_eq_signedPermutationOrbit
    {p : ℕ} [Fact p.Prime] {A B : ℤ}
    (hAB : A ^ 2 + B ^ 2 = (p : ℤ)) :
    twoSquarePrimePopulation p = signedPermutationOrbit A B := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  ext q
  obtain ⟨u, v⟩ := q
  constructor
  · intro hq
    have hnorm := (mem_twoSquarePrimePopulation_iff hp (u, v)).mp hq
    rcases two_sq_unique (Fact.out : p.Prime) hnorm hAB with hsame | hswap
    · change u ^ 2 = A ^ 2 ∧ v ^ 2 = B ^ 2 at hsame
      rcases sq_eq_sq_cases hsame.1 with hu | hu <;>
        rcases sq_eq_sq_cases hsame.2 with hv | hv <;>
        simp [signedPermutationOrbit, signOrbit, hu, hv]
    · change u ^ 2 = B ^ 2 ∧ v ^ 2 = A ^ 2 at hswap
      rcases sq_eq_sq_cases hswap.1 with hu | hu <;>
        rcases sq_eq_sq_cases hswap.2 with hv | hv <;>
        simp [signedPermutationOrbit, signOrbit, hu, hv]
  · intro hq
    rw [signedPermutationOrbit, Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases Finset.mem_product.mp hq with ⟨hu, hv⟩
      simp only [signOrbit, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        apply (mem_twoSquarePrimePopulation_iff hp _).mpr <;>
        simpa using hAB
    · rcases Finset.mem_product.mp hq with ⟨hu, hv⟩
      simp only [signOrbit, Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
        apply (mem_twoSquarePrimePopulation_iff hp _).mpr <;>
        nlinarith [hAB]

private theorem signOrbit_card {a : ℤ} (ha : a ≠ 0) :
    (signOrbit a).card = 2 := by
  unfold signOrbit
  rw [Finset.card_insert_of_notMem]
  · simp
  · simp only [Finset.mem_singleton]
    intro h
    apply ha
    omega

private theorem signOrbits_disjoint_of_parity
    {A B : ℤ} (hA : A % 2 = 1) (hB : B % 2 = 0) :
    Disjoint (signOrbit A) (signOrbit B) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  simp only [signOrbit, Finset.mem_insert, Finset.mem_singleton] at hxA hxB
  rcases hxA with rfl | rfl <;> rcases hxB with h | h <;> omega

theorem signedPermutationOrbit_card
    {A B : ℤ} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hA : A % 2 = 1) (hB : B % 2 = 0) :
    (signedPermutationOrbit A B).card = 8 := by
  have hdisjSigns := signOrbits_disjoint_of_parity hA hB
  have hdisjProducts :
      Disjoint (signOrbit A ×ˢ signOrbit B)
        (signOrbit B ×ˢ signOrbit A) := by
    rw [Finset.disjoint_left]
    intro q hleft hright
    have hleft' := Finset.mem_product.mp hleft
    have hright' := Finset.mem_product.mp hright
    exact (Finset.disjoint_left.mp hdisjSigns) hleft'.1 hright'.1
  rw [signedPermutationOrbit, Finset.card_union_of_disjoint hdisjProducts,
    Finset.card_product, Finset.card_product,
    signOrbit_card hA0, signOrbit_card hB0]

private theorem nat_prime_not_square {p a : ℕ} (hp : p.Prime)
    (h : a ^ 2 = p) : False := by
  have hprime : (a ^ 2).Prime := h.symm ▸ hp
  exact (Nat.Prime.not_prime_pow (x := a) (n := 2) (by omega)) hprime

/-- A prime congruent to one modulo four has a normalized two-square source:
the first coordinate is odd, the second even, and both are nonzero. -/
theorem exists_normalized_twoSquare_prime
    {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) :
    ∃ A B : ℤ,
      A ^ 2 + B ^ 2 = (p : ℤ) ∧ A % 2 = 1 ∧ B % 2 = 0 ∧
        A ≠ 0 ∧ B ≠ 0 := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq
    (p := p) (by omega : p % 4 ≠ 3)
  rcases a.even_or_odd with ⟨u, hu⟩ | ⟨u, hu⟩ <;>
    rcases b.even_or_odd with ⟨v, hv⟩ | ⟨v, hv⟩
  · exfalso
    rw [hu, hv] at hab
    have hfactor : (u + u) ^ 2 + (v + v) ^ 2 =
        4 * (u ^ 2 + v ^ 2) := by ring
    rw [hfactor] at hab
    have hmod := congrArg (fun n : ℕ => n % 4) hab
    omega
  · refine ⟨(b : ℤ), (a : ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · simpa [add_comm] using (by exact_mod_cast hab :
        (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ))
    · rw [hv]
      omega
    · rw [hu]
      omega
    · intro hb0
      have hbNat : b = 0 := by exact_mod_cast hb0
      rw [hbNat, zero_pow (by omega), add_zero] at hab
      exact nat_prime_not_square (Fact.out : p.Prime) hab
    · intro ha0
      have haNat : a = 0 := by exact_mod_cast ha0
      rw [haNat, zero_pow (by omega), zero_add] at hab
      exact nat_prime_not_square (Fact.out : p.Prime) hab
  · refine ⟨(a : ℤ), (b : ℤ), ?_, ?_, ?_, ?_, ?_⟩
    · exact_mod_cast hab
    · rw [hu]
      omega
    · rw [hv]
      omega
    · intro ha0
      have haNat : a = 0 := by exact_mod_cast ha0
      rw [haNat, zero_pow (by omega), zero_add] at hab
      exact nat_prime_not_square (Fact.out : p.Prime) hab
    · intro hb0
      have hbNat : b = 0 := by exact_mod_cast hb0
      rw [hbNat, zero_pow (by omega), add_zero] at hab
      exact nat_prime_not_square (Fact.out : p.Prime) hab
  · exfalso
    rw [hu, hv] at hab
    have hfactor : (2 * u + 1) ^ 2 + (2 * v + 1) ^ 2 =
        4 * (u ^ 2 + u + v ^ 2 + v) + 2 := by ring
    rw [hfactor] at hab
    have hmod := congrArg (fun n : ℕ => n % 4) hab
    omega

/-- **EXACT GAUSSIAN PRIME CENSUS.** -/
theorem twoSquarePrimePopulation_card_of_mod_four_one
    {p : ℕ} [Fact p.Prime] (hp1 : p % 4 = 1) :
    (twoSquarePrimePopulation p).card = 8 := by
  obtain ⟨A, B, hAB, hA, hB, hA0, hB0⟩ :=
    exists_normalized_twoSquare_prime hp1
  rw [twoSquarePrimePopulation_eq_signedPermutationOrbit hAB]
  exact signedPermutationOrbit_card hA0 hB0 hA hB

private theorem int_square_emod_four
    (x : ℤ) : x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases x.even_or_odd with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    rw [hu, show (u + u) ^ 2 = 4 * u ^ 2 by ring]
    simp
  · right
    rw [hu, show (2 * u + 1) ^ 2 = 4 * (u ^ 2 + u) + 1 by ring]
    simp

/-- A prime congruent to three modulo four admits no integral two-square
source. -/
theorem twoSquarePrimePopulation_eq_empty_of_mod_four_three
    {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) :
    twoSquarePrimePopulation p = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro q hq
  have hnorm := (mem_twoSquarePrimePopulation_iff
    (Fact.out : p.Prime).pos q).mp hq
  have hp3Z : (p : ℤ) % 4 = 3 := by exact_mod_cast hp3
  have hmod := congrArg (fun z : ℤ => z % 4) hnorm
  rcases int_square_emod_four q.1 with hq₁ | hq₁ <;>
    rcases int_square_emod_four q.2 with hq₂ | hq₂ <;> omega

theorem twoSquarePrimePopulation_card_of_mod_four_three
    {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) :
    (twoSquarePrimePopulation p).card = 0 := by
  rw [twoSquarePrimePopulation_eq_empty_of_mod_four_three hp3]
  rfl

/-- The conventional quadratic-character face of the exact eight-or-zero
population. -/
theorem twoSquarePrimePopulation_card_character
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ((twoSquarePrimePopulation p).card : ℤ) =
      4 * (quadraticChar (ZMod p) (-1) + 1) := by
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by
    have hodd := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
    omega
  rcases hp4 with hp1 | hp3
  · rw [twoSquarePrimePopulation_card_of_mod_four_one hp1]
    have hminus : (-1 : ZMod p) ≠ 0 := by
      simp [show p ≠ 1 from (Fact.out : p.Prime).ne_one]
    have hsquare : IsSquare (-1 : ZMod p) :=
      ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hchar : quadraticChar (ZMod p) (-1) = 1 :=
      (quadraticChar_one_iff_isSquare hminus).mpr hsquare
    rw [hchar]
    norm_num
  · rw [twoSquarePrimePopulation_card_of_mod_four_three hp3]
    have hnotSquare : ¬ IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hchar : quadraticChar (ZMod p) (-1) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hnotSquare
    rw [hchar]
    norm_num

#print axioms twoSquarePrimePopulation_eq_signedPermutationOrbit
#print axioms signedPermutationOrbit_card
#print axioms exists_normalized_twoSquare_prime
#print axioms twoSquarePrimePopulation_card_of_mod_four_one
#print axioms twoSquarePrimePopulation_eq_empty_of_mod_four_three
#print axioms twoSquarePrimePopulation_card_character

end Soma.Holonics.Millennium.FamilyTunnellTwoSquarePrimeCensus
