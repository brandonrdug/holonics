import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# The trace of a primitive colour is `μ(n)`

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(§12) names two compressions of a colour to its colourless part: the norm, which multiplies the
gaps and gives `e^(Λ(n))` (`Mathematics/OrbitEnergy`), and the trace, which adds the colours. This
file proves the trace half of #410's (n).

[proved-standard; formal-checked] What is proved.

1. **Every root of unity has one order** (`sum_divisors_primitive`): the colours of every order
   `d ∣ n` together are the `n`-th roots of unity, each once.
2. **All the `n`-th roots of unity cancel** (`sum_nthRoots_one`): their sum is `1` for `n = 1` and
   `0` for `n > 1`.
3. **A primitive colour compresses to `μ(n)`** (`trace_primitive_colour`): by Möbius inversion,
   `∑_(ζ primitive of order n) ζ = μ(n)`. So the colourless shadow of an orbit is `+1`, `−1` or
   `0`: `0` exactly when a prime repeats.

The Ramanujan sums `c_n(j)` (the trace of `ζ_n^j`) and the layer trace of a prime's tower remain
owed (#410 (n)); the record's receipt `colourless_tower.py` checks them exactly.

Consumers: the atlas row `colour.trace-compression`.
-/

namespace Holonics.Mathematics.ColourTrace

open ArithmeticFunction Finset Polynomial
open scoped ArithmeticFunction.Moebius

/-- [proved-standard; formal-checked] **Every root of unity has one order.** -/
theorem sum_divisors_primitive (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, ∑ ζ ∈ primitiveRoots d ℂ, ζ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ := by
  have : NeZero n := ⟨hn.ne'⟩
  rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion]
  intro i _ j _ hij
  exact IsPrimitiveRoot.disjoint hij

/-- [proved-standard; formal-checked] **All the `n`-th roots of unity cancel** when `n > 1`. -/
theorem sum_nthRoots_one {n : ℕ} (hn : 1 < n) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ζ = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp n (by omega)
  have hinj : Set.InjOn (fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / n) ^ i)
      (Finset.range n : Set ℕ) := fun i hi j hj hij =>
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  -- The powers `ζ^i`, `i < n`, are `n` distinct `n`-th roots of unity, hence all of them.
  have himage :
      (Finset.range n).image (fun i : ℕ => Complex.exp (2 * Real.pi * Complex.I / n) ^ i) =
        nthRootsFinset n (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset (by omega), pow_right_comm, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himage, Finset.sum_image hinj]
  exact hζ.geom_sum_eq_zero hn

/-- [proved-standard; formal-checked] **A primitive colour compresses to `μ(n)`.** -/
theorem trace_primitive_colour {n : ℕ} (hn : 0 < n) :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ = (μ n : ℂ) := by
  have h : ∀ m > 0, ∑ d ∈ m.divisors, (∑ ζ ∈ primitiveRoots d ℂ, ζ) =
      (if m = 1 then (1 : ℂ) else 0) := by
    intro m hm
    split_ifs with h1
    · subst h1
      simp [IsPrimitiveRoot.primitiveRoots_one]
    · rw [sum_divisors_primitive m hm]
      exact sum_nthRoots_one (by omega)
  have hinv := (sum_eq_iff_sum_smul_moebius_eq.mp h) n hn
  rw [← hinv, Finset.sum_eq_single (n, 1)]
  · simp
  · rintro ⟨a, b⟩ hab hne
    have hb : b ≠ 1 := by
      intro hb1
      subst hb1
      apply hne
      simp only [Nat.mem_divisorsAntidiagonal, mul_one] at hab
      rw [hab.1]
    simp [hb]
  · intro hnot
    exact absurd (by simp [Nat.mem_divisorsAntidiagonal, hn.ne']) hnot

end Holonics.Mathematics.ColourTrace
