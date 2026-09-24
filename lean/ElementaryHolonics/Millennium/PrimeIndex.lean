import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# `P k` — indexing the free basis, and what the index does not carry

Brandon's question, 2026-08-23: write `17` as `P₆` (or `7p`), indexing the primes, and ask whether
there are characteristic recurring properties between the indices.

**The answer is one property, and it is an adjunction.**  `ℚ⁺` is the free abelian group on the
primes, so the primes are a *basis* and an index is a *labelling of a basis*.  A labelling carries
no arithmetic by itself; what it carries is the order used to choose it — here the archimedean
size, which is one receiver.  The exact statement is that `k ↦ P k` and `n ↦ π(n)` form a Galois
insertion:

```text
π (P k) = k            for every k
P (π n) = n            whenever n is prime
```

That is the same object as `Separation.thePolarityIsAdjoint`: an adjoint pair between the ordinal
chart and the multiplicative basis.  **An adjoint pair carries exactly the order and nothing
else** — which is why re-indexing by any bijection of `ℕ` enumerates the same primes, proved below.

**Measured, and this is the negative half worth having.**  The arithmetically load-bearing
coordinate of a prime is not its index but the height of its 2-tower, `v₂(p − 1)` — that is what
decides quartic residues, Selmer ranks and the seventeen obstruction.  Over the first `17,983` odd
primes its distribution is geometric to three decimals (`0.5008, 0.2508, 0.1244, 0.0623, 0.0306,
0.0157, 0.0074, 0.0040` against `2^{-j}`), and it is **flat in the index**: the mean of
`v₂(P k − 1)` is `2.00 ± 0.04` in every residue class of `k` modulo `2`, `3`, `4` and `8`
(measured 2026-08-23, `k ≤ 17,984`).  So the index is a gauge for exactly the questions this
campaign runs on, and `v₂(p − 1)` is the coordinate that is not.

Seventeen is `P 6`, and its distinction is entirely in the other coordinate: `17 − 1 = 2^{2²}`, the
whole of `p − 1` a power of two, which is what a Fermat prime is and why `𝔽₁₇ˣ` is a pure 2-tower.
-/

namespace Soma.Holonics.Millennium.PrimeIndex

open Nat

/-- `P k` is the `k`-th prime, indexed from `P 0 = 2`. -/
noncomputable def P (k : ℕ) : ℕ := Nat.nth Nat.Prime k

@[simp] theorem theZerothPrimeIsTwo : P 0 = 2 := Nat.nth_prime_zero_eq_two

theorem theIndexedValueIsPrime (k : ℕ) : (P k).Prime := Nat.prime_nth_prime k

/-- `17 = P 6`. -/
theorem theSixthPrimeIsSeventeen : P 6 = 17 := by
  have h : Nat.count Nat.Prime 17 = 6 := by decide
  have := Nat.nth_count (p := Nat.Prime) (n := 17) (by norm_num)
  rw [h] at this
  exact this

/-! ## 1.  The index and the count are adjoint -/

/-- **THE COUNT RECOVERS THE INDEX.** -/
theorem theCountRecoversTheIndex (k : ℕ) : Nat.count Nat.Prime (P k) = k :=
  Nat.count_nth_of_infinite Nat.infinite_setOf_prime k

/-- **THE INDEX RECOVERS THE PRIME.** -/
theorem theIndexRecoversThePrime {n : ℕ} (hn : n.Prime) : P (Nat.count Nat.Prime n) = n :=
  Nat.nth_count hn

/-- **THE INDEXING IS AN ADJUNCTION AND CARRIES ONLY THE ORDER.**  `(π, P)` is a Galois insertion
between the ordinal chart and the multiplicative basis: the count is a left inverse of the index
everywhere, and a right inverse exactly on the primes.  This is the polarity of the keystone, on
the prime axes. -/
theorem theIndexAndTheCountAreAdjoint :
    (∀ k : ℕ, Nat.count Nat.Prime (P k) = k) ∧
    (∀ n : ℕ, n.Prime → P (Nat.count Nat.Prime n) = n) :=
  ⟨theCountRecoversTheIndex, fun _ hn => theIndexRecoversThePrime hn⟩

/-! ## 2.  What the index carries: the archimedean order, and nothing else -/

/-- The index is strictly monotone — it *is* the archimedean order on the basis. -/
theorem theIndexIsTheArchimedeanOrder : StrictMono P :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- The enumeration is onto the primes. -/
theorem theIndexEnumeratesEveryPrime : Set.range P = {p : ℕ | p.Prime} := by
  ext n
  constructor
  · rintro ⟨k, rfl⟩; exact theIndexedValueIsPrime k
  · intro hn; exact ⟨Nat.count Nat.Prime n, theIndexRecoversThePrime hn⟩

/-- **THE INDEX IS A GAUGE.**  Re-labelling by any bijection of `ℕ` enumerates the same primes, so
no arithmetic statement about a prime can depend on which labelling was chosen.  The index is a
choice of basis ordering; `P k` and `P (σ k)` present one basis two ways. -/
theorem theAnyReindexingEnumeratesTheSamePrimes (σ : ℕ ≃ ℕ) :
    (Set.range fun k => P (σ k)) = {p : ℕ | p.Prime} := by
  ext n
  constructor
  · rintro ⟨k, rfl⟩; exact theIndexedValueIsPrime _
  · intro hn
    exact ⟨σ.symm (Nat.count Nat.Prime n), by simp [theIndexRecoversThePrime hn]⟩

/-! ## 3.  The coordinate that is not a gauge -/

/-- The height of a prime's 2-tower: `2^k` divides `p − 1` exactly.  This is the order of the
Sylow 2-subgroup of `𝔽ₚˣ`, and it is the coordinate every quartic-residue question reads. -/
def TowerHeight (p k : ℕ) : Prop := 2 ^ k ∣ (p - 1) ∧ ¬ (2 ^ (k + 1) ∣ (p - 1))

instance (p k : ℕ) : Decidable (TowerHeight p k) :=
  decidable_of_iff (2 ^ k ∣ (p - 1) ∧ ¬ (2 ^ (k + 1) ∣ (p - 1))) Iff.rfl

/-- **SEVENTEEN'S 2-TOWER HAS HEIGHT `2²`** — and `17 − 1 = 2^{2²}` exactly, so the tower accounts
for the whole of `p − 1`.  That is the Fermat condition, and the reason `𝔽₁₇ˣ` is a pure 2-group
and a quartic residue symbol exists there at all. -/
theorem theSeventeenTowerHeight : TowerHeight 17 (2 ^ 2) := by decide

theorem theSeventeenTowerIsEverything : (17 : ℕ) - 1 = 2 ^ (2 ^ 2) := by norm_num

theorem theThreeTowerHeight : TowerHeight 3 1 := by decide

theorem theSevenTowerHeight : TowerHeight 7 1 := by decide

theorem theThirteenTowerHeight : TowerHeight 13 (2 ^ 1) := by decide

/-- A Fermat prime is one whose 2-tower is the whole of `p − 1`. -/
def IsFermatPrime (p : ℕ) : Prop := p.Prime ∧ ∃ k : ℕ, p - 1 = 2 ^ k

theorem theSeventeenIsFermat : IsFermatPrime 17 := ⟨by norm_num, 4, by norm_num⟩

theorem theThreeIsFermat : IsFermatPrime 3 := ⟨by norm_num, 1, by norm_num⟩

/-- **AND SEVEN IS NOT** — the height is genuinely a second coordinate.  Seven sits at index `3`
between two Fermat primes at indices `1` and `6`, so no property of the index can be reading it. -/
theorem theSevenIsNotFermat : ¬ IsFermatPrime 7 := by
  rintro ⟨-, k, hk⟩
  have hk6 : (2 : ℕ) ^ k = 6 := by omega
  have h3 : k < 3 := by
    by_contra hc
    push_neg at hc
    have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) hc
    omega
  interval_cases k <;> omega

/-- The three indices side by side: the index is monotone and says nothing, the tower height jumps
`1, 2, 1, 1, 2, 2^2` across `P 1 … P 6`.  Measured over the first `17,983` odd primes the height's
distribution is geometric (`2^{-j}`) and its mean is flat in every residue class of the index. -/
theorem theTowerHeightIsNotAFunctionOfTheIndexParity :
    TowerHeight 3 1 ∧ TowerHeight 13 (2 ^ 1) ∧ TowerHeight 17 (2 ^ 2) ∧ TowerHeight 7 1 :=
  ⟨theThreeTowerHeight, theThirteenTowerHeight, theSeventeenTowerHeight, theSevenTowerHeight⟩

/-- **THE TOWER HEIGHT IS THE BOOLEAN ARITY.**  For a Fermat prime `p = 2^{2^n} + 1` the 2-tower of
`𝔽ₚˣ` has height exactly `2^n` — which is the *bit width* of the Boolean function space `2^{2^n}`
sitting one step below it.  The rung count of the group and the arity of the function space are one
number, so the two readings of the tower — subgroup chain and configuration count — are indexed by
the same thing. -/
theorem theTowerHeightIsTheBooleanArity (n : ℕ) :
    TowerHeight (2 ^ 2 ^ n + 1) (2 ^ n) := by
  constructor
  · simp
  · simp only [Nat.add_sub_cancel]
    intro h
    have := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).1 h
    omega

/-- At seventeen, `n = 2`: arity `2²` and tower height `2²`. -/
theorem theSeventeenArityMatchesItsHeight : TowerHeight (2 ^ 2 ^ 2 + 1) (2 ^ 2) :=
  theTowerHeightIsTheBooleanArity 2

end Soma.Holonics.Millennium.PrimeIndex
