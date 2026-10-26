import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# An orbit's gaps multiply to its prime: the orbit energy is the von Mangoldt weight

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(§5 and §12) reads the primitive `d`-th roots of unity as the colours of one Galois orbit and
`1 − ζ` as a colour's gap, and owes (j) the orbit energy and the norm half of (n) to #410.

[proved-standard; formal-checked] What is proved.

1. **The gaps of one orbit multiply to `Φ_d(1)`** (`orbit_gap_product`): over `ℂ`,
   `∏_(ζ primitive of order d) (1 − ζ) = Φ_d(1)`.
2. **`Φ_d(1)` is the orbit's prime or 1** (`cyclotomic_eval_one`): for `d ≥ 2`, `Φ_d(1)` is the
   least prime factor of `d` when `d` is a prime power, and `1` otherwise, in every commutative ring.
3. **The orbit energy is `Λ`** (`cyclotomic_eval_one_eq_exp_vonMangoldt`,
   `orbit_gap_product_eq_exp_vonMangoldt`): for `d ≥ 2`, `Φ_d(1) = e^(Λ(d))`. Only prime-power
   orbits carry energy, and a repetition `p^k` carries the primitive weight `log p`. This is the
   norm compression `N(1 − ζ_d) = e^(Λ(d))` of §12.
4. **A ring's orbits multiply to its size** (`orbit_energies_multiply_to_ring`): for `m ≥ 1`,
   `∏_(d | m, d ≠ 1) Φ_d(1) = m`, so the orbit energies of ring `m` add to `log m`.
5. **The orbit energy in product form** (`prod_divisors_zpow_neg_moebius`,
   `prod_divisors_zpow_neg_moebius_eq_cyclotomic`): `∏_(d ∣ n) d^(−μ(d)) = e^(Λ(n))` for every
   `n`, the Möbius inversion of `∑_(d ∣ n) Λ(d) = log n`; for `n ≥ 2` it is `Φ_n(1)`, so
   `N(1 − ζ_n) = ∏_(d ∣ n) d^(−μ(d))`. The orbit's energy is read off the sizes of the rings below
   it, each with the sign of its own count of primes.

Consumers: the atlas rows `colour.orbit-energy` and `colour.trace-compression` (its norm half).
-/

namespace Holonics.Mathematics.OrbitEnergy

open Polynomial ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- [proved-standard; formal-checked] **`Φ_d(1)` is the orbit's prime or 1.** -/
theorem cyclotomic_eval_one (R : Type*) [CommRing R] {n : ℕ} (hn : 2 ≤ n) :
    (cyclotomic n R).eval 1 = if IsPrimePow n then (n.minFac : R) else 1 := by
  split_ifs with h
  · obtain ⟨p, k, hp, hk, rfl⟩ := h
    have hp' : p.Prime := Nat.prime_iff.mpr hp
    have := Fact.mk hp'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [eval_one_cyclotomic_prime_pow, hp'.pow_minFac (Nat.succ_ne_zero j)]
  · have hnp : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, p ^ k ≠ n := by
      intro p hp k hk
      rcases k with _ | k
      · simp at hk
        omega
      · exact h ⟨p, k + 1, hp.prime, k.succ_pos, hk⟩
    exact eval_one_cyclotomic_not_prime_pow hnp

/-- [proved-standard; formal-checked] **The orbit energy is the von Mangoldt weight.** -/
theorem cyclotomic_eval_one_eq_exp_vonMangoldt {n : ℕ} (hn : 2 ≤ n) :
    (cyclotomic n ℝ).eval 1 = Real.exp (Λ n) := by
  rw [cyclotomic_eval_one ℝ hn, vonMangoldt_apply]
  split_ifs
  · rw [Real.exp_log (by exact_mod_cast Nat.minFac_pos n)]
  · rw [Real.exp_zero]

/-- [proved-standard; formal-checked] **The gaps of one orbit multiply to `Φ_d(1)`.** -/
theorem orbit_gap_product {n : ℕ} (hn : 0 < n) :
    ∏ ζ ∈ primitiveRoots n ℂ, (1 - ζ) = (cyclotomic n ℂ).eval 1 := by
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne'),
    eval_prod]
  simp

/-- [proved-standard; formal-checked] **An orbit's gaps multiply to `e^(Λ(d))`.** -/
theorem orbit_gap_product_eq_exp_vonMangoldt {n : ℕ} (hn : 2 ≤ n) :
    ∏ ζ ∈ primitiveRoots n ℂ, (1 - ζ) = (Real.exp (Λ n) : ℂ) := by
  rw [orbit_gap_product (by omega), cyclotomic_eval_one ℂ hn, vonMangoldt_apply]
  split_ifs
  · rw [Real.exp_log (by exact_mod_cast Nat.minFac_pos n)]
    push_cast
    rfl
  · simp

/-- [proved-standard; formal-checked] **A ring's orbits multiply to its size.** -/
theorem orbit_energies_multiply_to_ring (R : Type*) [CommRing R] {m : ℕ} (hm : 0 < m) :
    ∏ d ∈ m.divisors.erase 1, (cyclotomic d R).eval 1 = m := by
  rw [← eval_prod, prod_cyclotomic_eq_geom_sum hm]
  simp

/-- [proved-standard; formal-checked] **The orbit energy in product form:**
`∏_(d ∣ n) d^(−μ(d)) = e^(Λ(n))`, by Möbius inversion of `∑_(d ∣ n) Λ(d) = log n`. -/
theorem prod_divisors_zpow_neg_moebius (n : ℕ) :
    ∏ d ∈ n.divisors, (d : ℝ) ^ (-μ d) = Real.exp (Λ n) := by
  have h : ∀ d ∈ n.divisors, (d : ℝ) ^ (-μ d) = Real.exp (-((μ d : ℝ) * Real.log d)) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos hd0]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl h, ← Real.exp_sum, Finset.sum_neg_distrib, sum_moebius_mul_log_eq,
    neg_neg]

/-- [proved-standard; formal-checked] **The norm of a gap in product form:** for `n ≥ 2`,
`∏_(d ∣ n) d^(−μ(d)) = Φ_n(1)`. -/
theorem prod_divisors_zpow_neg_moebius_eq_cyclotomic {n : ℕ} (hn : 2 ≤ n) :
    ∏ d ∈ n.divisors, (d : ℝ) ^ (-μ d) = (cyclotomic n ℝ).eval 1 := by
  rw [prod_divisors_zpow_neg_moebius, cyclotomic_eval_one_eq_exp_vonMangoldt hn]

end Holonics.Mathematics.OrbitEnergy
