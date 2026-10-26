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
4. **All the `m`-th roots of unity hear a mode only when it is a whole turn**
   (`sum_nthRoots_pow`): `∑_(ζ^m = 1) ζ^j` is `m` when `m ∣ j` and `0` otherwise.
5. **The trace of `ζ_n^j` is the Ramanujan sum** (`ramanujan_sum`):
   `∑_(ζ primitive of order n) ζ^j = c_n(j) = ∑_(d ∣ gcd(n, j)) μ(n/d)·d`. At `j = 1` it is
   `trace_primitive_colour`.
6. **A layer of a prime's tower keeps the old colours and erases the new** (`layer_fixes_below`,
   `layer_trace`): for `ω` of order `p^(k+1)`, the `p` moves `ω ↦ ω^(1 + i·p^k)` fix `ω^p`, which
   generates the layer below, and `∑_(i<p) ω^(j(1 + i·p^k))` is `p·ω^j` when `p ∣ j` and `0`
   otherwise.

With these, #410's (n) is discharged: the norm half is `Mathematics/OrbitEnergy`.

Consumers: the atlas rows `colour.trace-compression` and `colour.colour-tower`.
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

/-- [proved-standard; formal-checked] **All the `m`-th roots of unity hear a mode only when it is a
whole turn:** `∑_(ζ^m = 1) ζ^j = m` when `m ∣ j`, and `0` otherwise. -/
theorem sum_nthRoots_pow {m : ℕ} (hm : 0 < m) (j : ℕ) :
    ∑ ζ ∈ nthRootsFinset m (1 : ℂ), ζ ^ j = if m ∣ j then (m : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp m hm.ne'
  set ω := Complex.exp (2 * Real.pi * Complex.I / m) with hω
  have hinj : Set.InjOn (fun i : ℕ => ω ^ i) (Finset.range m : Set ℕ) := fun i hi k hk hik =>
    hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hk) hik
  have himage : (Finset.range m).image (fun i : ℕ => ω ^ i) = nthRootsFinset m (1 : ℂ) := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      rw [Polynomial.mem_nthRootsFinset hm, pow_right_comm, hζ.pow_eq_one, one_pow]
    · rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hinj, Finset.card_range]
  rw [← himage, Finset.sum_image hinj]
  simp_rw [← pow_mul, mul_comm _ j, pow_mul]
  split_ifs with hdvd
  · rw [(hζ.pow_eq_one_iff_dvd j).mpr hdvd]
    simp
  · have hne : ω ^ j ≠ 1 := fun h => hdvd ((hζ.pow_eq_one_iff_dvd j).mp h)
    have hpow : (ω ^ j) ^ m = 1 := by rw [pow_right_comm, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- [proved-standard; formal-checked] **The trace of `ζ_n^j` is the Ramanujan sum:**
`∑_(ζ primitive of order n) ζ^j = ∑_(d ∣ gcd(n, j)) μ(n/d)·d`. -/
theorem ramanujan_sum {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ ^ j =
      ∑ d ∈ n.divisors.filter (· ∣ j), ((μ (n / d) : ℤ) : ℂ) * d := by
  have h : ∀ m > 0, ∑ d ∈ m.divisors, (∑ ζ ∈ primitiveRoots d ℂ, ζ ^ j) =
      (if m ∣ j then (m : ℂ) else 0) := by
    intro m hm
    have : NeZero m := ⟨hm.ne'⟩
    rw [← sum_nthRoots_pow hm j, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
      Finset.sum_biUnion]
    intro a _ b _ hab
    exact IsPrimitiveRoot.disjoint hab
  have hinv := (sum_eq_iff_sum_smul_moebius_eq.mp h) n hn
  rw [← hinv, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℤ) • (if b ∣ j then (b : ℂ) else 0)),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · rw [zsmul_eq_mul]
  · simp

/-- [proved-standard; formal-checked] **A layer's moves fix the layer below:** for `ω` of order
`p^(k+1)`, `(ω^(1 + i·p^k))^p = ω^p`. -/
theorem layer_fixes_below {R : Type*} [CommRing R] {ω : R} {p k : ℕ}
    (hω : IsPrimitiveRoot ω (p ^ (k + 1))) (i : ℕ) :
    (ω ^ (1 + i * p ^ k)) ^ p = ω ^ p := by
  rw [← pow_mul, add_mul, one_mul, pow_add, mul_assoc, ← pow_succ, pow_mul',
    hω.pow_eq_one, one_pow, mul_one]

/-- [proved-standard; formal-checked] **A layer keeps the old colours and erases the new:**
`∑_(i<p) ω^(j(1 + i·p^k))` is `p·ω^j` when `p ∣ j`, and `0` otherwise. -/
theorem layer_trace {R : Type*} [CommRing R] [IsDomain R] {ω : R} {p k : ℕ} (hp : p.Prime)
    (hω : IsPrimitiveRoot ω (p ^ (k + 1))) (j : ℕ) :
    ∑ i ∈ range p, ω ^ (j * (1 + i * p ^ k)) = if p ∣ j then (p : R) * ω ^ j else 0 := by
  have hη : IsPrimitiveRoot (ω ^ p ^ k) p :=
    IsPrimitiveRoot.pow (pow_pos hp.pos _) hω (by rw [pow_succ])
  have hterm : ∀ i, ω ^ (j * (1 + i * p ^ k)) = ω ^ j * ((ω ^ p ^ k) ^ j) ^ i := by
    intro i
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  simp_rw [hterm, ← mul_sum]
  split_ifs with hdvd
  · obtain ⟨c, rfl⟩ := hdvd
    rw [pow_mul (ω ^ p ^ k), hη.pow_eq_one, one_pow]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  · have hprim : IsPrimitiveRoot ((ω ^ p ^ k) ^ j) p :=
      hη.pow_of_coprime j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd).symm
    rw [hprim.geom_sum_eq_zero hp.one_lt, mul_zero]

end Holonics.Mathematics.ColourTrace
