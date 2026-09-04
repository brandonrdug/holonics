import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# The prime simplex: the Mertens function is minus its reduced Euler characteristic

The squarefree numbers at most `N` are the faces of a simplicial complex on the primes,

```
    K_N = { S ⊂ primes : ∏_{p ∈ S} p ≤ N },
```

closed under subsets because a sub-product is smaller.  A face with `Ω(n) = k` primes is a
`(k − 1)`-simplex; `n = 1` is the empty face.  The Möbius polarity `μ(n) = (−1)^{Ω(n)}` is the
orientation by dimension parity, so the Mertens function is minus the reduced Euler
characteristic:

```
    M(N) = Σ_{n ≤ N} μ(n) = Σ_{F ∈ K_N} (−1)^{|F|} = −χ̃(K_N).
```

`K_N` is a *shifted* complex — replace a prime by a smaller prime and the product drops — so by
Björner–Kalai it is homotopy equivalent to a wedge of spheres whose `(k−1)`-th Betti number is the
number of faces avoiding the least vertex `2` whose join with `2` leaves the complex: the odd
squarefree `m ∈ (N/2, N]` with `Ω(m) = k`.  This file proves the identities that reading rests
on, exactly and for every `N`:

* `reducedEuler_eq_neg_mertens` — `χ̃(K_N) = −M(N)`;
* `mertens_eq_oddOctave` — `M(N) = Σ_{odd m ∈ (N/2, N]} μ(m)`, the homology living in the top
  octave (the elementary content is `μ(2m) = −μ(m)` for odd `m` and `0` for even `m`);
* `mertens_eq_alternating_octave` — `M(N) = Σ_k (−1)^k · #{odd squarefree m ∈ (N/2, N] : Ω(m) = k}`,
  the alternating count over the sphere generators graded by prime count.

The identification of those counts with Betti numbers is the Björner–Kalai theorem for shifted
complexes and is *not* proved here; the counts are named `octaveCount`, and the interpretation is
stated as such.  The weighted characteristic `Σ_S (−1)^{|S|} (∏S)^{−s} = 1/ζ(s)` has its poles at
the zeros, so the zeros are the modes of `χ`; `RH ⟺ M(N) = O(N^{1/2+ε})` is Titchmarsh 14.25(C)
and is recorded as a named port, not asserted.

Every theorem below is discharged with no `sorryAx`.
-/

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

namespace Soma.Holonics.Millennium.PrimeSimplex

/-- [definition] The Mertens function `M(N) = Σ_{0 < n ≤ N} μ(n)`. -/
def mertens (N : ℕ) : ℤ := ∑ n ∈ Ioc 0 N, μ n

/-- [definition] The faces of the prime simplex `K_N`: the squarefree `n ≤ N`, `n = 1` the empty
face, `n` the shadow of the face `{p : p ∣ n}` under `∏`. -/
def faces (N : ℕ) : Finset ℕ := (Ioc 0 N).filter Squarefree

/-- [definition] The reduced Euler characteristic `Σ_F (−1)^{dim F}` with `dim = Ω(n) − 1`. -/
def reducedEuler (N : ℕ) : ℤ := ∑ n ∈ faces N, -((-1 : ℤ) ^ Ω n)

/-- [proved-derived; formal-checked] **The Mertens function is minus the reduced Euler
characteristic of the prime simplex.**  Non-squarefree `n` are not faces and carry `μ(n) = 0`;
squarefree `n` carry `μ(n) = (−1)^{Ω(n)}`, the polarity of the face. -/
theorem reducedEuler_eq_neg_mertens (N : ℕ) : reducedEuler N = -mertens N := by
  unfold reducedEuler mertens faces
  rw [sum_filter, ← sum_neg_distrib]
  apply sum_congr rfl
  intro n _
  by_cases h : Squarefree n
  · simp [h, moebius_apply_of_squarefree h]
  · simp [h, moebius_eq_zero_of_not_squarefree h]

/-- [proved-derived; formal-checked] Doubling: `μ(2k) = −μ(k)` for odd `k`, `0` for even `k`. -/
theorem moebius_two_mul (k : ℕ) : μ (2 * k) = if Odd k then -μ k else 0 := by
  split_ifs with hk
  · have hc : Nat.Coprime 2 k := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hk.not_two_dvd_nat
    rw [isMultiplicative_moebius.map_mul_of_coprime hc, moebius_apply_prime Nat.prime_two]
    ring
  · apply moebius_eq_zero_of_not_squarefree
    obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hk
    intro hsq
    have h4 : 2 * 2 ∣ 2 * (j + j) := ⟨j, by ring⟩
    exact absurd (hsq 2 h4) (by decide)

/-- [definition] `Σ_{odd m ≤ N} μ(m)`. -/
def oddSum (N : ℕ) : ℤ := ∑ m ∈ Ioc 0 N, if Odd m then μ m else 0

theorem mertens_succ (n : ℕ) : mertens (n + 1) = mertens n + μ (n + 1) := by
  unfold mertens
  rw [sum_Ioc_succ_top (Nat.zero_le _)]

theorem oddSum_succ (n : ℕ) :
    oddSum (n + 1) = oddSum n + if Odd (n + 1) then μ (n + 1) else 0 := by
  unfold oddSum
  rw [sum_Ioc_succ_top (Nat.zero_le _)]

/-- [proved-derived; formal-checked] `M(N) = Σ_{odd m ≤ N} μ(m) − Σ_{odd m ≤ N/2} μ(m)`. -/
theorem mertens_eq_oddSum_sub (N : ℕ) : mertens N = oddSum N - oddSum (N / 2) := by
  induction N with
  | zero => simp [mertens, oddSum]
  | succ n ih =>
    rw [mertens_succ, ih]
    rcases Nat.even_or_odd n with hn | hn
    · obtain ⟨k, hk⟩ := hn
      have h1 : (n + 1) / 2 = n / 2 := by omega
      have hodd : Odd (n + 1) := ⟨k, by omega⟩
      rw [h1, oddSum_succ, if_pos hodd]
      ring
    · obtain ⟨k, hk⟩ := hn
      have h1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have hne : ¬ Odd (n + 1) := by
        rw [Nat.not_odd_iff_even]
        exact ⟨k + 1, by omega⟩
      have h3 : n + 1 = 2 * (n / 2 + 1) := by omega
      rw [h1, oddSum_succ n, if_neg hne, add_zero, oddSum_succ (n / 2)]
      rw [h3, moebius_two_mul]
      split_ifs <;> ring

/-- [definition] The odd Möbius sum over the top octave `(N/2, N]`. -/
def oddOctave (N : ℕ) : ℤ := ∑ m ∈ (Ioc (N / 2) N).filter Odd, μ m

theorem oddSum_sub_eq_oddOctave (N : ℕ) : oddSum N - oddSum (N / 2) = oddOctave N := by
  unfold oddSum oddOctave
  rw [sum_filter]
  have h := sum_Ioc_consecutive (fun m => if Odd m then (μ m : ℤ) else 0)
    (Nat.zero_le (N / 2)) (Nat.div_le_self N 2)
  linarith [h]

/-- [proved-derived; formal-checked] **The homology of the prime simplex lives in the top
octave:** `M(N) = Σ_{odd m ∈ (N/2, N]} μ(m)`. -/
theorem mertens_eq_oddOctave (N : ℕ) : mertens N = oddOctave N := by
  rw [mertens_eq_oddSum_sub, oddSum_sub_eq_oddOctave]

/-- [definition] The odd squarefree members of the top octave with exactly `k` prime factors.
For `k ≥ 1` these are the sphere generators of dimension `k − 1` (Björner–Kalai, interpretation;
not proved here); `k = 0` counts the empty face when `N ≤ 1`. -/
def octaveCount (N k : ℕ) : ℕ :=
  ((Ioc (N / 2) N).filter (fun m => Odd m ∧ Squarefree m ∧ Ω m = k)).card

/-- The odd squarefree top octave. -/
def oddSquarefreeOctave (N : ℕ) : Finset ℕ :=
  (Ioc (N / 2) N).filter (fun m => Odd m ∧ Squarefree m)

theorem oddOctave_eq_sum_oddSquarefreeOctave (N : ℕ) :
    oddOctave N = ∑ m ∈ oddSquarefreeOctave N, (-1 : ℤ) ^ Ω m := by
  unfold oddOctave oddSquarefreeOctave
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases ho : Odd m
  · by_cases hs : Squarefree m
    · simp [ho, hs, moebius_apply_of_squarefree hs]
    · simp [ho, hs, moebius_eq_zero_of_not_squarefree hs]
  · simp [ho]

theorem octaveCount_eq (N k : ℕ) :
    octaveCount N k = ((oddSquarefreeOctave N).filter (fun m => Ω m = k)).card := by
  unfold octaveCount oddSquarefreeOctave
  rw [filter_filter]
  congr 1
  apply filter_congr
  intro m _
  simp [and_assoc]

/-- [proved-derived; formal-checked] **The alternating count of the sphere generators, graded by
prime count, is the Mertens function**: `M(N) = Σ_k (−1)^k · octaveCount N k`, summed over the
prime counts actually occurring. -/
theorem mertens_eq_alternating_octave (N : ℕ) :
    mertens N =
      ∑ k ∈ (oddSquarefreeOctave N).image Ω, (-1 : ℤ) ^ k * octaveCount N k := by
  rw [mertens_eq_oddOctave, oddOctave_eq_sum_oddSquarefreeOctave]
  rw [← sum_fiberwise_of_maps_to (s := oddSquarefreeOctave N)
    (t := (oddSquarefreeOctave N).image Ω) (g := Ω) (fun m hm => mem_image_of_mem _ hm)]
  apply sum_congr rfl
  intro k _
  rw [sum_congr rfl (fun m hm => by rw [(mem_filter.mp hm).2]), sum_const, nsmul_eq_mul,
    mul_comm, octaveCount_eq]

/-! ## The receiver: Mertens growth, and the named equivalence port -/

/-- [definition] The Mertens growth receiver `M(N) = O(N^{1/2+ε})` for every `ε > 0`. -/
def MertensGrowth : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
    |(mertens N : ℝ)| ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε)

/-- [project-postulate] The classical equivalence `RH ⟺ MertensGrowth` (Titchmarsh, *The Theory of
the Riemann Zeta-Function*, 14.25(C)).  A port: it is named, not asserted. -/
structure HasMertensEquivalence : Prop where
  equivalence : RiemannHypothesis ↔ MertensGrowth

/-- [proved-derived; formal-checked] Under the port, the Riemann hypothesis is a growth law on
the reduced Euler characteristic of the prime simplex. -/
theorem riemannHypothesis_iff_reducedEuler_growth (port : HasMertensEquivalence) :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |(reducedEuler N : ℝ)| ≤ C * (N : ℝ) ^ ((1 : ℝ) / 2 + ε) := by
  rw [port.equivalence]
  unfold MertensGrowth
  simp only [reducedEuler_eq_neg_mertens, Int.cast_neg, abs_neg]

section Audit

#print axioms reducedEuler_eq_neg_mertens
#print axioms mertens_eq_oddOctave
#print axioms mertens_eq_alternating_octave
#print axioms riemannHypothesis_iff_reducedEuler_growth

end Audit

end Soma.Holonics.Millennium.PrimeSimplex
