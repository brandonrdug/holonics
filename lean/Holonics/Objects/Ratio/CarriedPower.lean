import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Objects.Ratio.CarriedPower: the carried power `2^(n + k/L)` in `ℚ(θ)`, `θ^L = 2`

[definition] The ratio's exponentiated chart at a grain (rebuild step 4, addition 4; Rust owner
`holonics::ratio::exponentiated::{CarriedPower, PhaseField}`). A rational exponent read at a grain
`L` is carried as a carry `n`, an exact shift by `2^n`, and a phase class `k ∈ ℤ/L`, a power of the
grain root `θ` of `ℚ(θ) = ℚ[X]/(X^L − 2)`.

[proved-derived; formal-checked] `X^L − 2` is Eisenstein at `2` over `ℤ` and so irreducible over `ℚ`
(`irreducible_X_pow_sub_two_int`, `irreducible_X_pow_sub_two`, Gauss's lemma); `θ^L = 2`
(`theta_pow`); the phase carry is multiplication by `2` (`k + L ↦ n + 1`), carried powers multiply
with carry, `ℚ(θ)` is a field so normalization there is exact division, and the real chart
`θ ↦ 2^(1/L)` sends `2^n θ^k` to `2^(n + k/L)` (`carriedPower_exact`). A positive grain is
load-bearing (`zero_grain_is_not_a_field`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.Ratio.CarriedPower

section CarriedPower

open Polynomial

/-- [proved-derived; formal-checked] **`X^L − 2` is Eisenstein at `2`** over `ℤ`. -/
theorem irreducible_X_pow_sub_two_int {L : ℕ} (hL : 0 < L) : Irreducible (X ^ L - C (2 : ℤ)) := by
  have hmonic : (X ^ L - C (2 : ℤ)).Monic := monic_X_pow_sub_C 2 hL.ne'
  have hprime : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
  refine irreducible_of_eisenstein_criterion hprime ?_ ?_ ?_ ?_ hmonic.isPrimitive
  · rw [hmonic.leadingCoeff, Ideal.mem_span_singleton]; norm_num
  · intro n hn
    rw [degree_X_pow_sub_C hL, Nat.cast_lt] at hn
    rw [coeff_sub, coeff_X_pow, coeff_C, if_neg hn.ne, Ideal.mem_span_singleton]
    split_ifs <;> simp
  · rw [degree_X_pow_sub_C hL]; exact_mod_cast hL
  · rw [coeff_sub, coeff_X_pow, coeff_C, if_neg (Ne.symm hL.ne'), if_pos rfl,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    norm_num

/-- [proved-derived; formal-checked] **`X^L − 2` is irreducible over `ℚ`** (Gauss's lemma). -/
theorem irreducible_X_pow_sub_two {L : ℕ} (hL : 0 < L) : Irreducible (X ^ L - C (2 : ℚ)) := by
  have hmonic : (X ^ L - C (2 : ℤ)).Monic := monic_X_pow_sub_C 2 hL.ne'
  have := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hmonic.isPrimitive).mp
    (irreducible_X_pow_sub_two_int hL)
  have hmap : (X ^ L - C (2 : ℤ)).map (Int.castRingHom ℚ) = X ^ L - C (2 : ℚ) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]; simp
  rwa [hmap] at this

variable (L : ℕ)

/-- [definition] The receiver's exact chart `ℚ(θ) = ℚ[X]/(X^L − 2)`. -/
abbrev PhaseField := AdjoinRoot (X ^ L - C (2 : ℚ))

/-- [definition] The grain root `θ`, `θ^L = 2`. -/
def theta : PhaseField L := AdjoinRoot.root _

/-- [definition] **The carried power** `2^n θ^k`: the carry `n` is an exact shift by `2^n`, and the
phase `k` a power of the grain root. -/
def carriedPower (n : ℤ) (k : ℕ) : PhaseField L :=
  algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ n) * theta L ^ k

theorem theta_pow : theta L ^ L = 2 := by
  have h := AdjoinRoot.eval₂_root (X ^ L - C (2 : ℚ))
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  rw [theta, h]
  exact map_ofNat _ 2

/-- [definition] The real root `2^(1/L)`. -/
def realRoot : ℝ := (2 : ℝ) ^ ((1 : ℝ) / L)

theorem realRoot_pow {L : ℕ} (hL : 0 < L) : realRoot L ^ L = 2 := by
  rw [realRoot, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : (1 : ℝ) / L * L = 1 := by field_simp
  rw [this, Real.rpow_one]

/-- [definition] The real chart `θ ↦ 2^(1/L)` of `ℚ(θ)`. -/
def realChart {L : ℕ} (hL : 0 < L) : PhaseField L →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftAlgHom (X ^ L - C (2 : ℚ)) (Algebra.ofId ℚ ℝ) (realRoot L) (by
    simp [realRoot_pow hL])

/-- [proved-derived; formal-checked] **The carried power is exact.**
* `θ^L = 2` in `ℚ(θ)`;
* the phase carry is multiplication by `2`: `2^n θ^(k+L) = 2^(n+1) θ^k`;
* carried powers multiply with carry: `(2^n θ^k)(2^m θ^l) = 2^(n+m+⌊(k+l)/L⌋) θ^((k+l) mod L)`;
* `ℚ(θ)` is a field (`X^L − 2` is irreducible), so normalization there is exact division;
* the real chart sends `2^n θ^k` to `2^(n + k/L)`. -/
theorem carriedPower_exact {L : ℕ} (hL : 0 < L) (n m : ℤ) (k l : ℕ) :
    theta L ^ L = 2 ∧
      carriedPower L n (k + L) = carriedPower L (n + 1) k ∧
      carriedPower L n k * carriedPower L m l =
        carriedPower L (n + m + ((k + l) / L : ℕ)) ((k + l) % L) ∧
      IsField (PhaseField L) ∧
      realChart hL (carriedPower L n k) = (2 : ℝ) ^ ((n : ℝ) + k / L) := by
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  refine ⟨theta_pow L, ?_, ?_, ?_, ?_⟩
  · simp only [carriedPower, pow_add, theta_pow, zpow_add_one₀ h2, map_mul, map_ofNat]
    ring
  · have hsplit : theta L ^ (k + l) = theta L ^ ((k + l) % L) * 2 ^ ((k + l) / L) := by
      conv_lhs => rw [← Nat.mod_add_div (k + l) L, pow_add, pow_mul, theta_pow]
    have h2map : algebraMap ℚ (PhaseField L) 2 = 2 := map_ofNat _ 2
    have hcast : algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ (n + m + ((k + l) / L : ℕ))) =
        algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ n) * algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ m) *
          2 ^ ((k + l) / L) := by
      rw [zpow_add₀ h2, zpow_add₀ h2, zpow_natCast, map_mul, map_mul, map_pow]
      simp only [h2map]
    simp only [carriedPower]
    rw [hcast]
    have hkl : theta L ^ k * theta L ^ l = theta L ^ ((k + l) % L) * 2 ^ ((k + l) / L) := by
      rw [← pow_add, hsplit]
    linear_combination (algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ n) *
      algebraMap ℚ (PhaseField L) ((2 : ℚ) ^ m)) * hkl
  · have : Fact (Irreducible (X ^ L - C (2 : ℚ))) := ⟨irreducible_X_pow_sub_two hL⟩
    exact Field.toIsField _
  · simp only [carriedPower, map_mul, map_pow, AlgHom.commutes, realChart, theta,
      AdjoinRoot.liftAlgHom_root]
    rw [eq_ratCast, Rat.cast_zpow, Rat.cast_ofNat, realRoot, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
    congr 1
    ring

/-- [counterexample; formal-checked] **A positive grain is load-bearing.** At `L = 0`,
`X^0 − 2 = −1` is a unit and `ℚ[X]/(−1)` is the zero ring, not a field. -/
theorem zero_grain_is_not_a_field : ¬ IsField (AdjoinRoot (X ^ 0 - C (2 : ℚ))) := by
  intro h
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  have hmk := AdjoinRoot.mk_self (f := (X ^ 0 - C (2 : ℚ)))
  have h1 : (1 : AdjoinRoot (X ^ 0 - C (2 : ℚ))) = 0 := by
    have : AdjoinRoot.mk (X ^ 0 - C (2 : ℚ)) (X ^ 0 - C 2) = 1 - 2 := by
      simp; exact map_ofNat _ 2
    rw [hmk] at this
    have h2 : (1 : AdjoinRoot (X ^ 0 - C (2 : ℚ))) =
        -((1 : AdjoinRoot (X ^ 0 - C (2 : ℚ))) - 2) := by ring
    rw [h2, ← this, neg_zero]
  exact hab (by rw [← mul_one a, ← mul_one b, h1, mul_zero, mul_zero])

end CarriedPower

section Audit

#print axioms irreducible_X_pow_sub_two_int
#print axioms irreducible_X_pow_sub_two
#print axioms theta_pow
#print axioms realRoot_pow
#print axioms carriedPower_exact
#print axioms zero_grain_is_not_a_field

end Audit

end Holonics.Objects.Ratio.CarriedPower
