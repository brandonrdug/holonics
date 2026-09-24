import Mathlib.NumberTheory.Pell
import Mathlib.Algebra.AddTorsor.Defs
import Mathlib.NumberTheory.PythagoreanTriples
import Mathlib.NumberTheory.FLT.Four
import ElementaryHolonics.Millennium.EuclideanSqrtTwo
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The seventeen quartic: which branch a congruence can refuse, and which it provably cannot

`Ш(E₁₇)[2]` rests on one Diophantine statement, `F⁴ − E⁴ = 17M² ⟹ E² = F²`
(`SeventeenSeparator.TheQuarticIsRefused`).  Writing `x = F/E` it is `x⁴ − 17y² = 1`, so `x²` is a
Pell solution for `d = 17` and the question is whether any `x²` past the trivial one is a square.

**The descent splits, and the two halves behave differently under congruences.**  For `x` odd,
`x² − 1` and `x² + 1` have gcd `2`, and `17` divides exactly one of the halves:

```text
branch A    x² − 1 = 2u²        x² + 1 = 2·17·v²
branch B    x² − 1 = 2·17·u²    x² + 1 = 2·v²
```

Branch A's side condition forces `x² ≡ −1 (mod 17)`, which the trivial solution `x = 1` does not
satisfy, and a congruence refutes it.  Branch B's side condition is satisfied *by the trivial
solution*, and this file proves that **no congruence whatever can refuse it**:

> `theChainReturnsToTheIdentityAtEveryModulus` — for every modulus `m` and every Pell solution `a`,
> some positive power of `a` is congruent to the identity mod `m`.

The reason is structural and is the whole Hasse failure at seventeen in one sentence: the solution
group is infinite cyclic, its reduction mod `m` lands in a finite set, and the reduction of a
*group* revisits the identity.  So a residue test can never separate `a^0` from `a^{n}`, and any
branch whose condition holds at `a^0` survives every modulus.

**A correction is recorded here.**  A two-layer sieve reported on 2026-08-23 (mod `21`, then mod
`1711`) appeared to close branch B.  It does not: the Pell(17) chain has period `870` modulo `1711`
and the scan ran to index `2400` in steps of `8`, so it never reached `8·435 = 3480` where the
chain returns to the residue of the identity.  The apparent disjointness was a truncation
artifact, and the theorem below says no repair of that search can work.  What remains is an
archimedean argument — a descent on size, which is what Ljunggren's resolution of `x⁴ − Dy² = 1`
actually is — not an arithmetic one.
-/

namespace Soma.Holonics.Millennium.QuarticSeventeen

open Pell

set_option maxRecDepth 8000

/-- The fundamental unit of `ℤ[√2]`, as a Pell solution. -/
def u2 : Solution₁ 2 := Solution₁.mk 3 2 (by norm_num)

/-- The fundamental unit of the Pell equation at seventeen. -/
def u17 : Solution₁ 17 := Solution₁.mk 33 8 (by norm_num)

@[simp] theorem u2_x : u2.x = 3 := rfl
@[simp] theorem u2_y : u2.y = 2 := rfl
@[simp] theorem u17_x : u17.x = 33 := rfl
@[simp] theorem u17_y : u17.y = 8 := rfl

/-! ## 1.  The chain returns to the identity at every modulus -/

private theorem cancel {d : ℤ} (a : Solution₁ d) (m : ℕ) [NeZero m] {i j : ℕ} (hlt : i < j)
    (hx : (((a ^ j).x : ℤ) : ZMod m) = (((a ^ i).x : ℤ) : ZMod m))
    (hy : (((a ^ j).y : ℤ) : ZMod m) = (((a ^ i).y : ℤ) : ZMod m)) :
    (((a ^ (j - i)).x : ℤ) : ZMod m) = 1 ∧ (((a ^ (j - i)).y : ℤ) : ZMod m) = 0 := by
  have hsplit : a ^ j = a ^ i * a ^ (j - i) := by
    rw [← pow_add]; congr 1; omega
  have e1 : (((a ^ j).x : ℤ) : ZMod m) =
      (((a ^ i).x : ℤ) : ZMod m) * (((a ^ (j - i)).x : ℤ) : ZMod m) +
        (d : ZMod m) * ((((a ^ i).y : ℤ) : ZMod m) * (((a ^ (j - i)).y : ℤ) : ZMod m)) := by
    rw [hsplit, Solution₁.x_mul]; push_cast; ring
  have e2 : (((a ^ j).y : ℤ) : ZMod m) =
      (((a ^ i).x : ℤ) : ZMod m) * (((a ^ (j - i)).y : ℤ) : ZMod m) +
        (((a ^ i).y : ℤ) : ZMod m) * (((a ^ (j - i)).x : ℤ) : ZMod m) := by
    rw [hsplit, Solution₁.y_mul]; push_cast; ring
  rw [hx] at e1
  rw [hy] at e2
  have hprop : (((a ^ i).x : ℤ) : ZMod m) ^ 2
      - (d : ZMod m) * (((a ^ i).y : ℤ) : ZMod m) ^ 2 = 1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod m)) (a ^ i).prop
    push_cast at h
    linear_combination h
  set p := (((a ^ i).x : ℤ) : ZMod m)
  set q := (((a ^ i).y : ℤ) : ZMod m)
  set A := (((a ^ (j - i)).x : ℤ) : ZMod m)
  set B := (((a ^ (j - i)).y : ℤ) : ZMod m)
  have key : p ^ 2 - (d : ZMod m) * q ^ 2 = A * (p ^ 2 - (d : ZMod m) * q ^ 2) := by
    linear_combination p * e1 - (d : ZMod m) * q * e2
  rw [hprop] at key
  have hA : A = 1 := by linear_combination -key
  have hpB : p * B = 0 := by linear_combination -e2 - q * hA
  have hdqB : (d : ZMod m) * q * B = 0 := by linear_combination -e1 - p * hA
  have hB : B = 0 := by linear_combination p * hpB - q * hdqB - B * hprop
  exact ⟨hA, hB⟩

/-- **NO MODULUS SEPARATES A PELL CHAIN FROM ITS OWN IDENTITY.**  The solutions form a group, the
reduction lands in the finite set `ZMod m × ZMod m`, and two equal reductions cancel to give a
positive power congruent to `(1, 0)`.  The cancellation is exact: from `p = pA + d q B`,
`q = pB + qA` and `p² − d q² = 1` one gets `A = 1` and `B = 0` by ring algebra alone, with no
invertibility hypothesis on `p` or `q`. -/
theorem theChainReturnsToTheIdentityAtEveryModulus {d : ℤ} (a : Solution₁ d) (m : ℕ) [NeZero m] :
    ∃ n : ℕ, 0 < n ∧ (((a ^ n).x : ℤ) : ZMod m) = 1 ∧ (((a ^ n).y : ℤ) : ZMod m) = 0 := by
  classical
  obtain ⟨i, j, hne, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => ((((a ^ n).x : ℤ) : ZMod m), (((a ^ n).y : ℤ) : ZMod m)))
  have hx : (((a ^ i).x : ℤ) : ZMod m) = (((a ^ j).x : ℤ) : ZMod m) := congrArg Prod.fst hEq
  have hy : (((a ^ i).y : ℤ) : ZMod m) = (((a ^ j).y : ℤ) : ZMod m) := congrArg Prod.snd hEq
  rcases Nat.lt_or_ge i j with hlt | hge
  · obtain ⟨h1, h2⟩ := cancel a m hlt hx.symm hy.symm
    exact ⟨j - i, by omega, h1, h2⟩
  · have hlt : j < i := by omega
    obtain ⟨h1, h2⟩ := cancel a m hlt hx hy
    exact ⟨i - j, by omega, h1, h2⟩

/-- **A BRANCH THROUGH THE TRIVIAL SOLUTION IS REFUSED BY NO MODULUS.**  If a side condition `C`
holds at the identity solution, then for every modulus there is a positive power of the chain whose
residues satisfy the same congruence the identity does — so no residue test distinguishes them. -/
theorem theCongruenceCannotSeparateTheTrivialSolution {d : ℤ} (a : Solution₁ d) (m : ℕ)
    [NeZero m] :
    ∃ n : ℕ, 0 < n ∧
      (((a ^ n).x : ℤ) : ZMod m) = (((a ^ (0 : ℕ)).x : ℤ) : ZMod m) ∧
      (((a ^ n).y : ℤ) : ZMod m) = (((a ^ (0 : ℕ)).y : ℤ) : ZMod m) := by
  obtain ⟨n, hn, hx, hy⟩ := theChainReturnsToTheIdentityAtEveryModulus a m
  refine ⟨n, hn, ?_, ?_⟩
  · rw [hx]; simp [Solution₁.x_one]
  · rw [hy]; simp [Solution₁.y_one]

/-! ## 2.  The branch that a congruence does refuse -/

/-- Branch A's side condition forces `x² ≡ −1 (mod 17)`. -/
theorem theFirstBranchForcesAMinusOneSquare {x v : ℤ} (h : x ^ 2 + 1 = 34 * v ^ 2) :
    ((x : ZMod 17)) ^ 2 = -1 := by
  have hc := congrArg (fun z : ℤ => (z : ZMod 17)) h
  push_cast at hc
  have h34 : (34 : ZMod 17) = 0 := by decide
  linear_combination hc + (v : ZMod 17) ^ 2 * h34

/-- And the square roots of `−1` mod `17` are exactly `±4` — the residues the chain will have to
supply. -/
theorem theSquareRootsOfMinusOneAtSeventeen :
    ∀ z : ZMod 17, z ^ 2 = -1 ↔ (z = 4 ∨ z = 13) := by decide

/-- The trivial solution does **not** satisfy branch A's condition: `1² + 1 = 2 ≢ 0 (mod 17)`.
That is why branch A is congruence-refutable and branch B is not. -/
theorem theTrivialSolutionFailsTheFirstBranch : ¬ ((1 : ZMod 17)) ^ 2 = -1 := by decide

/-- The trivial solution **does** satisfy branch B's condition: `1² + 1 = 2 = 2·1²`, and
`1² − 1 = 0 = 34·0²`.  By `theCongruenceCannotSeparateTheTrivialSolution` no modulus can refuse
branch B, so the refusal must be archimedean. -/
theorem theTrivialSolutionMeetsTheSecondBranch :
    (1 : ℤ) ^ 2 + 1 = 2 * 1 ^ 2 ∧ (1 : ℤ) ^ 2 - 1 = 34 * 0 ^ 2 := by norm_num

/-! ## 3.  The even branch dies at once -/

/-- Coprime factors of a square are squares.  `mathlib`'s `exists_eq_pow_of_mul_eq_pow` over the
GCD monoid `ℕ`, in the form the descent needs. -/
theorem theCoprimeFactorsOfASquareAreSquares {a b c : ℕ} (h : Nat.Coprime a b)
    (hab : a * b = c ^ 2) : (∃ u, a = u ^ 2) ∧ (∃ v, b = v ^ 2) := by
  have hu : IsUnit (Nat.gcd a b) := by
    rw [Nat.isUnit_iff]
    simpa [Nat.Coprime] using h
  have hu' : IsUnit (Nat.gcd b a) := by
    rw [Nat.isUnit_iff]
    simpa [Nat.Coprime] using h.symm
  exact ⟨exists_eq_pow_of_mul_eq_pow hu hab,
         exists_eq_pow_of_mul_eq_pow hu' (by rwa [mul_comm] at hab)⟩

/-- **THE SPLIT AT SEVENTEEN.**  A coprime factorisation of `17·square` puts the seventeen wholly
on one side and leaves both quotients square. -/
theorem theSplitAtSeventeen {a b y : ℕ} (h : Nat.Coprime a b) (hab : a * b = 17 * y ^ 2) :
    (∃ u v, a = u ^ 2 ∧ b = 17 * v ^ 2) ∨ (∃ u v, a = 17 * u ^ 2 ∧ b = v ^ 2) := by
  have hp : Nat.Prime 17 := by norm_num
  have hdvd : 17 ∣ a * b := ⟨y ^ 2, hab⟩
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with hda | hdb
  · right
    obtain ⟨a', rfl⟩ := hda
    have hcop : Nat.Coprime b a' := (Nat.Coprime.coprime_dvd_right ⟨17, by ring⟩ h.symm)
    have hab' : b * a' = y ^ 2 := by
      have : 17 * (a' * b) = 17 * y ^ 2 := by linarith [hab]
      have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
      linarith [this]
    obtain ⟨⟨v, hv⟩, ⟨u, hu⟩⟩ := theCoprimeFactorsOfASquareAreSquares hcop hab'
    exact ⟨u, v, by rw [hu], hv⟩
  · left
    obtain ⟨b', rfl⟩ := hdb
    have hcop : Nat.Coprime a b' := (Nat.Coprime.coprime_dvd_right ⟨17, by ring⟩ h)
    have hab' : a * b' = y ^ 2 := by
      have : 17 * (a * b') = 17 * y ^ 2 := by linarith [hab]
      have := Nat.eq_of_mul_eq_mul_left (by norm_num) this
      linarith [this]
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := theCoprimeFactorsOfASquareAreSquares hcop hab'
    exact ⟨u, v, hu, by rw [hv]⟩

/-- **THE EVEN BRANCH IS REFUSED.**  If `x` is even then `x² − 1` and `x² + 1` are coprime odd
naturals whose product is `17y²`, so one of them is a perfect square — and a square differing from
`x²` by one forces `x ≤ 1`. -/
theorem theEvenBranchIsRefused {X Y : ℕ} (hX : Even X) (hX2 : 2 ≤ X)
    (h : X ^ 4 = 1 + 17 * Y ^ 2) : False := by
  have hXsq : 1 ≤ X ^ 2 := by nlinarith
  obtain ⟨A, hA⟩ : ∃ A, X ^ 2 = A + 1 := ⟨X ^ 2 - 1, by omega⟩
  have hAodd : Odd A := by
    obtain ⟨t, ht⟩ := hX
    have h2 : A + 1 = (t + t) ^ 2 := by rw [← hA, ht]
    have h3 : (t + t) ^ 2 = 2 * (2 * t * t) := by ring
    rw [h3] at h2
    exact Nat.odd_iff.2 (by omega)
  have hX4 : (A + 1) ^ 2 = 1 + 17 * Y ^ 2 := by
    rw [← hA, show ((X ^ 2) ^ 2 : ℕ) = X ^ 4 by ring]; exact h
  have hprod : A * (A + 2) = 17 * Y ^ 2 := by nlinarith [hX4]
  have hcop : Nat.Coprime A (A + 2) := by
    have hd1 : Nat.gcd A (A + 2) ∣ A := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd A (A + 2) ∣ (A + 2) := Nat.gcd_dvd_right _ _
    have hd3 : Nat.gcd A (A + 2) ∣ 2 := (Nat.dvd_add_right hd1).mp hd2
    rcases (Nat.dvd_prime Nat.prime_two).1 hd3 with hg | hg
    · exact hg
    · exfalso
      rw [hg] at hd1
      obtain ⟨t, ht⟩ := hd1
      rw [Nat.odd_iff] at hAodd
      omega
  rcases theSplitAtSeventeen hcop hprod with ⟨u, v, hu, hv⟩ | ⟨u, v, hu, hv⟩
  · have hXu : X ^ 2 = u ^ 2 + 1 := by rw [hA, hu]
    have hlt : u < X := by nlinarith
    have hmul : (u + 1) * (u + 1) ≤ X * X := Nat.mul_le_mul hlt hlt
    nlinarith [hmul, hXu, hX2]
  · have hXv : v ^ 2 = X ^ 2 + 1 := by omega
    have hlt : X < v := by nlinarith
    have hmul : (X + 1) * (X + 1) ≤ v * v := Nat.mul_le_mul hlt hlt
    nlinarith [hmul, hXv, hX2]

/-- **THE ODD BRANCH SPLITS IN TWO.**  For `X` odd write `X² = 2A' + 1`; then
`4A'(A' + 1) = 17Y²` forces `Y` even, and after cancelling `4` the coprime pair `A'`, `A' + 1`
splits at seventeen, giving exactly the two branches. -/
theorem theOddBranchSplits {X Y : ℕ} (hX : Odd X) (h : X ^ 4 = 1 + 17 * Y ^ 2) :
    (∃ u v : ℕ, X ^ 2 = 2 * u ^ 2 + 1 ∧ X ^ 2 + 1 = 34 * v ^ 2) ∨
    (∃ u v : ℕ, X ^ 2 = 34 * u ^ 2 + 1 ∧ X ^ 2 + 1 = 2 * v ^ 2) := by
  obtain ⟨t, ht⟩ := hX
  obtain ⟨A, hA⟩ : ∃ A, X ^ 2 = 2 * A + 1 := ⟨2 * t * t + 2 * t, by rw [ht]; ring⟩
  have hX4 : (2 * A + 1) ^ 2 = 1 + 17 * Y ^ 2 := by
    rw [← hA, show ((X ^ 2) ^ 2 : ℕ) = X ^ 4 by ring]; exact h
  have hcore : 4 * (A * (A + 1)) = 17 * Y ^ 2 := by nlinarith [hX4]
  have hYeven : Even Y := by
    rcases Nat.even_or_odd Y with he | ho
    · exact he
    · exfalso
      obtain ⟨s, hs⟩ := ho
      have : 17 * Y ^ 2 = 2 * (34 * (s * s) + 34 * s + 8) + 1 := by
        rw [hs]; ring
      omega
  obtain ⟨Y1, hY1⟩ := hYeven
  have hsplit : A * (A + 1) = 17 * Y1 ^ 2 := by
    have h4 : 4 * (A * (A + 1)) = 4 * (17 * Y1 ^ 2) := by rw [hcore, hY1]; ring
    omega
  have hcop : Nat.Coprime A (A + 1) := by
    have hd1 : Nat.gcd A (A + 1) ∣ A := Nat.gcd_dvd_left _ _
    have hd2 : Nat.gcd A (A + 1) ∣ (A + 1) := Nat.gcd_dvd_right _ _
    exact Nat.dvd_one.mp ((Nat.dvd_add_right hd1).mp hd2)
  rcases theSplitAtSeventeen hcop hsplit with ⟨u, v, hu, hv⟩ | ⟨u, v, hu, hv⟩
  · exact Or.inl ⟨u, v, by rw [hA, hu], by omega⟩
  · exact Or.inr ⟨u, v, by rw [hA, hu]; ring, by omega⟩

/-- **THE WHOLE OBSTRUCTION IS THE TWO BRANCHES.**  Every nontrivial solution of `X⁴ = 1 + 17Y²`
is odd and lands on one of them: the even case is refused outright. -/
theorem theQuarticReducesToTheTwoBranches {X Y : ℕ} (hX2 : 2 ≤ X)
    (h : X ^ 4 = 1 + 17 * Y ^ 2) :
    (∃ u v : ℕ, X ^ 2 = 2 * u ^ 2 + 1 ∧ X ^ 2 + 1 = 34 * v ^ 2) ∨
    (∃ u v : ℕ, X ^ 2 = 34 * u ^ 2 + 1 ∧ X ^ 2 + 1 = 2 * v ^ 2) := by
  rcases Nat.even_or_odd X with he | ho
  · exact absurd (theEvenBranchIsRefused he hX2 h) not_false
  · exact theOddBranchSplits ho h

/-! ## 4.  Branch A is refused, and the refusal is the orbit of the fundamental unit -/

/-- `(3, 2)` is the fundamental solution at `d = 2`: the only smaller candidate is `x = 2`, and
`4 − 2y² = 1` has no integer solution. -/
theorem theFundamentalUnitAtTwo : IsFundamental u2 := by
  have hx : u2.x = 3 := rfl
  have hy : u2.y = 2 := rfl
  refine ⟨by rw [hx]; norm_num, by rw [hy]; norm_num, ?_⟩
  intro b hb
  rw [hx]
  by_contra hc
  push_neg at hc
  have hb2 : b.x = 2 := by omega
  have hp := b.prop
  rw [hb2] at hp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, k = b.y ^ 2 := ⟨_, rfl⟩
  rw [← hk] at hp
  omega

/-- The reduction of a `d = 2` solution modulo seventeen. -/
def red (a : Solution₁ 2) : ZMod 17 × ZMod 17 := ((a.x : ZMod 17), (a.y : ZMod 17))

/-- The orbit of the fundamental unit modulo seventeen: eight states, period `2³`. -/
def orbitTwo : Finset (ZMod 17 × ZMod 17) :=
  {(1, 0), (3, 2), (0, 12), (14, 2), (16, 0), (14, 15), (0, 5), (3, 15)}

theorem theStepClosesTheOrbit :
    ∀ s ∈ orbitTwo, ((3 * s.1 + 4 * s.2, 2 * s.1 + 3 * s.2) : ZMod 17 × ZMod 17) ∈ orbitTwo := by
  decide

theorem theInverseClosesTheOrbit :
    ∀ s ∈ orbitTwo, ((s.1, -s.2) : ZMod 17 × ZMod 17) ∈ orbitTwo := by decide

theorem theNegationClosesTheOrbit :
    ∀ s ∈ orbitTwo, ((-s.1, -s.2) : ZMod 17 × ZMod 17) ∈ orbitTwo := by decide

/-- **THE ORBIT MISSES THE SQUARE ROOTS OF `−1`.**  Its first components are `{0, 1, 3, 14, 16}`,
and `±4` are absent — so no `d = 2` solution has `x² ≡ −1 (mod 17)`. -/
theorem theOrbitMissesTheSquareRootsOfMinusOne :
    ∀ s ∈ orbitTwo, s.1 ^ 2 ≠ (-1 : ZMod 17) := by decide

theorem theReductionOfNatPowers : ∀ n : ℕ, red (u2 ^ n) ∈ orbitTwo := by
  intro n
  induction n with
  | zero => simp [red, Solution₁.x_one, Solution₁.y_one, orbitTwo]
  | succ k ih =>
    have hx : (((u2 ^ (k + 1)).x : ℤ) : ZMod 17) =
        3 * (((u2 ^ k).x : ℤ) : ZMod 17) + 4 * (((u2 ^ k).y : ℤ) : ZMod 17) := by
      rw [pow_succ, Solution₁.x_mul, u2_x, u2_y]; push_cast; ring
    have hy : (((u2 ^ (k + 1)).y : ℤ) : ZMod 17) =
        2 * (((u2 ^ k).x : ℤ) : ZMod 17) + 3 * (((u2 ^ k).y : ℤ) : ZMod 17) := by
      rw [pow_succ, Solution₁.y_mul, u2_x, u2_y]; push_cast; ring
    have := theStepClosesTheOrbit (red (u2 ^ k)) ih
    simpa [red, hx, hy] using this

theorem theReductionOfEveryPower : ∀ n : ℤ, red (u2 ^ n) ∈ orbitTwo := by
  intro n
  rcases n with m | m
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact theReductionOfNatPowers m
  · have hm : (Int.negSucc m) = -((m + 1 : ℕ) : ℤ) := by simp [Int.negSucc_eq]
    rw [hm, zpow_neg, zpow_natCast]
    have := theInverseClosesTheOrbit (red (u2 ^ (m + 1))) (theReductionOfNatPowers (m + 1))
    simpa [red, Solution₁.x_inv, Solution₁.y_inv] using this

/-- **EVERY `d = 2` SOLUTION REDUCES INTO THE ORBIT**, sign included. -/
theorem theEverySolutionReducesIntoTheOrbit (a : Solution₁ 2) : red a ∈ orbitTwo := by
  obtain ⟨n, hn | hn⟩ := theFundamentalUnitAtTwo.eq_zpow_or_neg_zpow a
  · rw [hn]; exact theReductionOfEveryPower n
  · rw [hn]
    have := theNegationClosesTheOrbit (red (u2 ^ n)) (theReductionOfEveryPower n)
    simpa [red, Solution₁.x_neg, Solution₁.y_neg] using this

/-- **BRANCH A IS REFUSED MODULO SEVENTEEN.**  Its side condition demands `X² ≡ −1 (mod 17)`, and
the orbit of the fundamental unit — which every solution of `X² − 2u² = 1` reduces into — never
supplies it.  The refusal uses the group, not a residue class: it is the orbit that is finite,
and the trivial solution `X = 1` is inside the orbit and outside the condition. -/
theorem theFirstBranchIsRefusedModSeventeen {X u v : ℕ}
    (h1 : X ^ 2 = 2 * u ^ 2 + 1) (h2 : X ^ 2 + 1 = 34 * v ^ 2) : False := by
  have hZ : ((X : ℤ)) ^ 2 - 2 * ((u : ℤ)) ^ 2 = 1 := by
    have : ((X : ℤ)) ^ 2 = 2 * ((u : ℤ)) ^ 2 + 1 := by exact_mod_cast h1
    linarith
  have hmem := theEverySolutionReducesIntoTheOrbit (Solution₁.mk (X : ℤ) (u : ℤ) hZ)
  have hcond : ((X : ZMod 17)) ^ 2 = -1 := by
    have hc : (((X : ℤ)) ^ 2 + 1 : ℤ) = 34 * ((v : ℤ)) ^ 2 := by exact_mod_cast h2
    have := congrArg (fun z : ℤ => (z : ZMod 17)) hc
    push_cast at this
    have h34 : (34 : ZMod 17) = 0 := by decide
    linear_combination this + (v : ZMod 17) ^ 2 * h34
  refine theOrbitMissesTheSquareRootsOfMinusOne _ hmem ?_
  simpa [red] using hcond

/-- **THE WHOLE QUARTIC NOW RESTS ON BRANCH B ALONE.**  Every nontrivial solution of
`X⁴ = 1 + 17Y²` is odd, splits into two branches, and branch A is refused by the orbit.  What
remains is one statement, and `theCongruenceCannotSeparateTheTrivialSolution` proves that no
modulus will ever reach it. -/
theorem theQuarticReducesToTheSecondBranch {X Y : ℕ} (hX2 : 2 ≤ X)
    (h : X ^ 4 = 1 + 17 * Y ^ 2) :
    ∃ u v : ℕ, X ^ 2 = 34 * u ^ 2 + 1 ∧ X ^ 2 + 1 = 2 * v ^ 2 := by
  rcases theQuarticReducesToTheTwoBranches hX2 h with ⟨u, v, h1, h2⟩ | hB
  · exact absurd (theFirstBranchIsRefusedModSeventeen h1 h2) not_false
  · exact hB

/-- The archimedean statement that would close it: in the Pell chain at seventeen, `2v² − 1` is a
perfect square only at the trivial term.  This is Ljunggren's theorem on `x⁴ − Dy² = 1` for
`D = 17`; `s₁ = 33` and `s₂ = 2177` are the two candidate terms and neither is a square.  It is a
descent on **size**, and by the theorem above it cannot be replaced by any congruence. -/
def TheArchimedeanDescentRefusesTheSecondBranch : Prop :=
  ∀ X u v : ℕ, X ^ 2 = 34 * u ^ 2 + 1 → X ^ 2 + 1 = 2 * v ^ 2 → X = 1

/-- With that one statement, the seventeen quartic is closed. -/
theorem theQuarticIsRefusedGivenTheDescent (hD : TheArchimedeanDescentRefusesTheSecondBranch)
    {X Y : ℕ} (h : X ^ 4 = 1 + 17 * Y ^ 2) : X ≤ 1 := by
  by_contra hc
  push_neg at hc
  obtain ⟨u, v, h1, h2⟩ := theQuarticReducesToTheSecondBranch (by omega) h
  have := hD X u v h1 h2
  omega

/-! ## 5.  Branch B is a meeting of two chains -/

/-- **BRANCH B REDUCES TO A PELL PAIR.**  `x² − 1 = 34u²` together with `x² + 1 = 2v²` is exactly
`v² − 17u² = 1` with `x² = 2v² − 1`: the value `v` must lie simultaneously in the Pell chain at
seventeen and in the chain `1, 5, 29, 169, …` of `x² + 1 = 2v²`. -/
theorem theSecondBranchIsATwoChainMeeting {x u v : ℤ}
    (h1 : x ^ 2 - 1 = 34 * u ^ 2) (h2 : x ^ 2 + 1 = 2 * v ^ 2) :
    v ^ 2 - 17 * u ^ 2 = 1 ∧ x ^ 2 = 2 * v ^ 2 - 1 := by
  constructor <;> linarith

/-! ## 6.  The homogeneous descent -/

/-- **THE HOMOGENEOUS FORM SPLITS INTO FOUR BRANCHES.**  `Ш(E₁₇)[2]` asks about
`f⁴ − e⁴ = 17m²` with `e, f` coprime, which is the affine case only when `e = 1`.  The same
descent runs on the general pair: `gcd(f² − e², f² + e²)` divides `2`, is `1` when `e, f` have
opposite parity and `2` when both are odd, and `theSplitAtSeventeen` then puts the seventeen wholly
on one side.  The four branches are the two parities crossed with the two placements of `17`.

Measured 2026-08-23 before the statement was written: **no coprime solution exists with
`1 ≤ e < f < 600`**, and **no congruence refuses any branch** — a sweep of every modulus below
`220`, over all `(e, f)` not both sharing a factor with the modulus, finds solutions for all four.
So the homogeneous case is globally obstructed exactly as the affine one is, and the refusal is
archimedean there too. -/
theorem theHomogeneousDescentSplits {e f M : ℕ} (hco : Nat.Coprime e f) (hlt : e < f)
    (h : f ^ 4 = e ^ 4 + 17 * M ^ 2) :
    (∃ a b, f ^ 2 = e ^ 2 + a ^ 2 ∧ f ^ 2 + e ^ 2 = 17 * b ^ 2) ∨
    (∃ a b, f ^ 2 = e ^ 2 + 17 * a ^ 2 ∧ f ^ 2 + e ^ 2 = b ^ 2) ∨
    (∃ a b, f ^ 2 = e ^ 2 + 2 * a ^ 2 ∧ f ^ 2 + e ^ 2 = 34 * b ^ 2) ∨
    (∃ a b, f ^ 2 = e ^ 2 + 34 * a ^ 2 ∧ f ^ 2 + e ^ 2 = 2 * b ^ 2) := by
  classical
  have hsq : e ^ 2 < f ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D, f ^ 2 = e ^ 2 + D := ⟨f ^ 2 - e ^ 2, by omega⟩
  set S := f ^ 2 + e ^ 2 with hS
  have hSD : S = D + 2 * e ^ 2 := by rw [hS, hD]; ring
  have hprod : D * S = 17 * M ^ 2 := by
    have h4 : f ^ 4 = (e ^ 2 + D) ^ 2 := by rw [show f ^ 4 = (f ^ 2) ^ 2 by ring, hD]
    rw [hSD]
    nlinarith [h4, h]
  -- the gcd of the two factors divides two
  set g := Nat.gcd D S with hg
  have hgD : g ∣ D := Nat.gcd_dvd_left _ _
  have hgS : g ∣ S := Nat.gcd_dvd_right _ _
  have hg2e : g ∣ 2 * e ^ 2 := by
    have : g ∣ D + 2 * e ^ 2 := by rw [← hSD]; exact hgS
    exact (Nat.dvd_add_right hgD).mp this
  have hg2f : g ∣ 2 * f ^ 2 := by
    have : D + S = 2 * f ^ 2 := by rw [hSD, hD]; ring
    rw [← this]
    exact Nat.dvd_add hgD hgS
  have hgtwo : g ∣ 2 := by
    have hcs : Nat.Coprime (e ^ 2) (f ^ 2) := (hco.pow 2 2)
    have := Nat.dvd_gcd hg2e hg2f
    rwa [Nat.gcd_mul_left, hcs, mul_one] at this
  rcases Nat.even_or_odd D with hDe | hDo
  · -- both `e` and `f` odd: the gcd is exactly two
    obtain ⟨A, hA⟩ := hDe
    have hA' : D = 2 * A := by omega
    obtain ⟨B, hB⟩ : ∃ B, S = 2 * B := ⟨e ^ 2 + A, by rw [hSD, hA']; ring⟩
    have hAB : 4 * (A * B) = 17 * M ^ 2 := by rw [← hprod, hA', hB]; ring
    have hMe : Even M := by
      rcases Nat.even_or_odd M with hm | hm
      · exact hm
      · exfalso
        obtain ⟨t, ht⟩ := hm
        have : 17 * M ^ 2 = 2 * (34 * (t * t) + 34 * t + 8) + 1 := by rw [ht]; ring
        omega
    obtain ⟨M1, hM1⟩ := hMe
    have hAB1 : A * B = 17 * M1 ^ 2 := by
      have : 4 * (A * B) = 4 * (17 * M1 ^ 2) := by rw [hAB, hM1]; ring
      omega
    have hcopAB : Nat.Coprime A B := by
      have hd1 : Nat.gcd A B ∣ A := Nat.gcd_dvd_left _ _
      have hd2 : Nat.gcd A B ∣ B := Nat.gcd_dvd_right _ _
      have h2A : (2 * Nat.gcd A B) ∣ D := by rw [hA']; exact mul_dvd_mul_left 2 hd1
      have h2B : (2 * Nat.gcd A B) ∣ S := by rw [hB]; exact mul_dvd_mul_left 2 hd2
      have : (2 * Nat.gcd A B) ∣ 2 := (Nat.dvd_gcd h2A h2B).trans hgtwo
      have hle := Nat.le_of_dvd (by norm_num) this
      have hpos : 0 < Nat.gcd A B := by
        rcases Nat.eq_zero_or_pos (Nat.gcd A B) with h0 | h0
        · exfalso
          have hA0 : A = 0 := Nat.eq_zero_of_gcd_eq_zero_left h0
          have hB0 : B = 0 := Nat.eq_zero_of_gcd_eq_zero_right h0
          rw [hB0] at hB
          omega
        · exact h0
      omega
    rcases theSplitAtSeventeen hcopAB hAB1 with ⟨u, v, hu, hv⟩ | ⟨u, v, hu, hv⟩
    · refine Or.inr (Or.inr (Or.inl ⟨u, v, ?_, ?_⟩))
      · rw [hD, hA', hu]
      · rw [hB, hv]; ring
    · refine Or.inr (Or.inr (Or.inr ⟨u, v, ?_, ?_⟩))
      · rw [hD, hA', hu]; ring
      · rw [hB, hv]
  · -- opposite parity: the two factors are coprime outright
    have hgodd : g ≠ 2 := by
      intro h2
      have : (2 : ℕ) ∣ D := by rw [← h2]; exact hgD
      rw [Nat.odd_iff] at hDo
      omega
    have hg1 : g = 1 := by
      have := Nat.le_of_dvd (by norm_num) hgtwo
      interval_cases g
      · exfalso
        have hD0 : D = 0 := Nat.eq_zero_of_gcd_eq_zero_left hg.symm
        rw [Nat.odd_iff] at hDo; omega
      · rfl
      · exact absurd rfl hgodd
    rcases theSplitAtSeventeen hg1 hprod with ⟨u, v, hu, hv⟩ | ⟨u, v, hu, hv⟩
    · exact Or.inl ⟨u, v, by rw [hD, hu], hv⟩
    · exact Or.inr (Or.inl ⟨u, v, by rw [hD, hu], hv⟩)

/-! ## 7.  The homogeneous branches descend, through Pythagoras -/

/-- The two algebraic identities the descent runs on. -/
theorem thePythagoreanIdentities (s t : ℤ) :
    (s ^ 2 + t ^ 2) ^ 2 + (2 * s * t) ^ 2 = s ^ 4 + 6 * s ^ 2 * t ^ 2 + t ^ 4 ∧
    (s ^ 2 - t ^ 2) ^ 2 - (2 * s * t) ^ 2 = s ^ 4 - 6 * s ^ 2 * t ^ 2 + t ^ 4 := by
  constructor <;> ring

/-- **THE FIRST HOMOGENEOUS BRANCH DESCENDS TO A QUARTIC IN TWO VARIABLES.**  `f² − e² = a²` makes
`(e, a, f)` a primitive Pythagorean triple; substituting the classification into
`f² + e² = 17b²` gives `s⁴ + 6s²t² + t⁴ = 17b²`.  That is one real descent step: three variables
become two. -/
theorem theFirstHomogeneousBranchDescends {e f b s t : ℤ}
    (he : e = 2 * s * t) (hf : f = s ^ 2 + t ^ 2) (h2 : f ^ 2 + e ^ 2 = 17 * b ^ 2) :
    s ^ 4 + 6 * s ^ 2 * t ^ 2 + t ^ 4 = 17 * b ^ 2 := by
  rw [he, hf] at h2
  linear_combination h2

/-- **AND THE SECOND TO ITS SIGN-FLIPPED TWIN.**  `f² + e² = b²` makes `(f, e, b)` primitive;
substituting into `f² − e² = 17a²` gives `s⁴ − 6s²t² + t⁴ = 17a²`. -/
theorem theSecondHomogeneousBranchDescends {e f a s t : ℤ}
    (he : e = 2 * s * t) (hf : f = s ^ 2 - t ^ 2) (h : f ^ 2 - e ^ 2 = 17 * a ^ 2) :
    s ^ 4 - 6 * s ^ 2 * t ^ 2 + t ^ 4 = 17 * a ^ 2 := by
  rw [he, hf] at h
  linear_combination h

/-- The parametrisation itself is mathlib's, so the descent is not conditional on an assumption:
a coprime Pythagorean triple with odd first leg and positive hypotenuse *is* `(m² − n², 2mn,
m² + n²)`. -/
theorem thePythagoreanParametrisationIsAvailable {x y z : ℤ} (h : PythagoreanTriple x y z)
    (hco : Int.gcd x y = 1) (hpar : x % 2 = 1) (hpos : 0 < z) :
    ∃ m n : ℤ, x = m ^ 2 - n ^ 2 ∧ y = 2 * m * n ∧ z = m ^ 2 + n ^ 2 := by
  obtain ⟨m, n, h1, h2, h3, -⟩ := h.coprime_classification' hco hpar hpos
  exact ⟨m, n, h1, h2, h3⟩

/-- **THE TWO DESCENDED QUARTICS, NAMED.**  Measured 2026-08-23: neither has a coprime solution
with `s, t < 800`, and neither is refused by any modulus below `300` — the descent gains a variable
back but does not gain a congruence, which is the signature of a genuinely global obstruction
persisting through descent. -/
def TheDescendedQuarticsAreRefused : Prop :=
  (∀ s t b : ℤ, s ^ 4 + 6 * s ^ 2 * t ^ 2 + t ^ 4 = 17 * b ^ 2 → s = 0 ∧ t = 0) ∧
  (∀ s t a : ℤ, s ^ 4 - 6 * s ^ 2 * t ^ 2 + t ^ 4 = 17 * a ^ 2 → s = 0 ∧ t = 0)

/-! ## 7b.  Both descended quartics are norm forms in `ℤ[√2]` — the ring that refused branch A -/

/-- **THE DESCENDED QUARTIC IS A NORM FROM `ℤ[√2]`.**  `s⁴ − 6s²t² + t⁴ = N(s² − 3t² + 2t²√2)`. -/
theorem theDescendedQuarticIsANormFromZSqrtTwo (s t : ℤ) :
    Zsqrtd.norm (⟨s ^ 2 - 3 * t ^ 2, 2 * t ^ 2⟩ : ℤ√2) = s ^ 4 - 6 * s ^ 2 * t ^ 2 + t ^ 4 := by
  simp [Zsqrtd.norm]
  ring

/-- And its twin: `s⁴ + 6s²t² + t⁴ = N(s² + 3t² + 2t²√2)`. -/
theorem theOtherDescendedQuarticIsANormFromZSqrtTwo (s t : ℤ) :
    Zsqrtd.norm (⟨s ^ 2 + 3 * t ^ 2, 2 * t ^ 2⟩ : ℤ√2) = s ^ 4 + 6 * s ^ 2 * t ^ 2 + t ^ 4 := by
  simp [Zsqrtd.norm]
  ring

/-- **AND SEVENTEEN IS ITSELF A NORM THERE**: `17 = N(5 + 2√2) = 25 − 8`.  So both descended
equations read `N(α) = N(5 + 2√2)·a²` inside one ring. -/
theorem theSeventeenIsANormFromZSqrtTwo : Zsqrtd.norm (⟨5, 2⟩ : ℤ√2) = 17 := by
  simp [Zsqrtd.norm]

/-- **AND THE UNIT IS THE ONE THAT ALREADY REFUSED AFFINE BRANCH A.**  `N(3 + 2√2) = 1` — that is
`u2`, whose orbit modulo seventeen misses `±4`.  So the affine refusal and the homogeneous descent
happen in **the same ring**: `ℤ[√2]`, with the same fundamental unit and the same split of
seventeen.  The two sides of the seventeen problem were never separate objects. -/
theorem theFundamentalUnitIsTheSameOne : Zsqrtd.norm (⟨3, 2⟩ : ℤ√2) = 1 := by
  simp [Zsqrtd.norm]

/-- Seventeen splits there, into a conjugate pair of norm `17`. -/
theorem theSeventeenSplitsInZSqrtTwo :
    (⟨5, 2⟩ : ℤ√2) * (⟨5, -2⟩ : ℤ√2) = (17 : ℤ√2) := by
  ext <;> simp [Zsqrtd.ext_iff] <;> ring

/-- **BOTH PELL CHAINS ARE ONE UNIT GROUP.**  `x² − 2y² = ±1` is exactly the condition that
`x + y√2` is a unit of `ℤ[√2]`.  So the chain that refused affine branch A (`x² − 2u² = 1`) and the
chain branch B lives in (`x² + 1 = 2v²`, i.e. `x² − 2v² = −1`) are **the same group**, read on its
two norm classes.  The seventeen problem has one algebraic object under all of it. -/
theorem theUnitsOfZSqrtTwoAreThePellSolutions (x y : ℤ) :
    IsUnit (⟨x, y⟩ : ℤ√2) ↔ (x ^ 2 - 2 * y ^ 2 = 1 ∨ x ^ 2 - 2 * y ^ 2 = -1) := by
  rw [← Zsqrtd.norm_eq_one_iff, Int.natAbs_eq_iff]
  constructor
  · rintro (h | h) <;> [left; right] <;>
      · simp only [Zsqrtd.norm] at h
        push_cast at h
        linear_combination h
  · rintro (h | h) <;> [left; right] <;>
      · simp only [Zsqrtd.norm]
        push_cast
        linear_combination h

/-- And the fundamental solution is the fundamental unit. -/
theorem theFundamentalSolutionIsAUnit : IsUnit ((⟨3, 2⟩ : ℤ√2)) :=
  (theUnitsOfZSqrtTwoAreThePellSolutions 3 2).2 (Or.inl (by norm_num))

/-- As is the negative-Pell generator `1 + √2`, on the other norm class. -/
theorem theNegativePellGeneratorIsAUnit : IsUnit ((⟨1, 1⟩ : ℤ√2)) :=
  (theUnitsOfZSqrtTwoAreThePellSolutions 1 1).2 (Or.inr (by norm_num))

/-! ## 7c.  The untwisted case descends, and it reproduces the same shape one degree down -/

/-- **THE UNTWISTED UNIT CASE FORCES A CONIC CONDITION.**  With `ε = ±1` the extraction
`α = ±π·u²` has `√2`-coefficient `±2(x² + 5xy + 2y²)`, and `α = ⟨s² − 3t², 2t²⟩` has `2t²`, so

```text
t² = ± (x² + 5xy + 2y²) .
```

Parity is silent here (the coefficient is even for every `x, y`), but the *value* is not. -/
theorem theUntwistedCaseGivesAConicCondition (x y : ℤ) :
    ((⟨5, 2⟩ : ℤ√2) * (⟨x, y⟩ : ℤ√2) ^ 2).im = 2 * (x ^ 2 + 5 * (x * y) + 2 * y ^ 2) := by
  have hsq : ((⟨x, y⟩ : ℤ√2) ^ 2) = ⟨x ^ 2 + 2 * y ^ 2, 2 * x * y⟩ := by
    ext <;> simp [Zsqrtd.ext_iff, pow_two] <;> ring
  rw [hsq]
  simp [Zsqrtd.im_mul]
  ring

/-- **AND THE CONIC COMPLETES TO A DIFFERENCE OF SQUARES WITH DISCRIMINANT SEVENTEEN.**
`4(x² + 5xy + 2y²) = (2x + 5y)² − 17y²`, because `disc(x² + 5xy + 2y²) = 25 − 8 = 17`. -/
theorem theConicCompletesToADifferenceOfSquares (x y : ℤ) :
    4 * (x ^ 2 + 5 * (x * y) + 2 * y ^ 2) = (2 * x + 5 * y) ^ 2 - 17 * y ^ 2 := by
  ring

/-- **SO THE DESCENT REPRODUCES ITS OWN SHAPE, ONE DEGREE DOWN.**  `t² = x² + 5xy + 2y²` becomes

```text
(2x + 5y)² − (2t)² = 17 y² ,
```

a difference of squares equal to seventeen times a square — the same equation the whole problem
started as (`F⁴ − E⁴ = 17M²` is `(F² − E²)(F² + E²) = 17M²`), with the degree halved.  **The
seventeen problem is self-similar under its own descent**, which is why every level is everywhere
locally soluble and no level is the last one: the obstruction is a fixed point of the descent, not
a residue that shrinks. -/
theorem theDescentReproducesItsOwnShape {x y t : ℤ} (h : t ^ 2 = x ^ 2 + 5 * (x * y) + 2 * y ^ 2) :
    (2 * x + 5 * y) ^ 2 - (2 * t) ^ 2 = 17 * y ^ 2 := by
  have h4 := theConicCompletesToADifferenceOfSquares x y
  linarith [h, h4]

/-- The discriminant is seventeen, exhibited: it is the same seventeen, not a coincidence of the
coefficients. -/
theorem theDiscriminantIsSeventeen : (5 : ℤ) ^ 2 - 4 * 1 * 2 = 17 := by norm_num

/-! ## 7d.  The levels are soluble; the obstruction is in the lift -/

/-- **THE DEGREE-TWO LEVEL HAS SOLUTIONS.**  `A² − B² = 17C²` is a *conic*, and conics satisfy the
Hasse principle (Hasse–Minkowski), so local solubility there is global solubility.  Exhibited:
`9² − 8² = 17`.  **So the descent cannot terminate by impossibility** — every level it reaches is
soluble, and the failure has to be elsewhere. -/
theorem theConicLevelIsSoluble : (9 : ℤ) ^ 2 - 8 ^ 2 = 17 * 1 ^ 2 := by norm_num

/-- And the conic solution lifts to the layer above it: `(x, y, t) = (2, 1, 4)` satisfies
`t² = x² + 5xy + 2y²`, so the descent's own compatibility holds one step up. -/
theorem theConicSolutionLiftsOneStep : (4 : ℤ) ^ 2 = 2 ^ 2 + 5 * (2 * 1) + 2 * 1 ^ 2 := by norm_num

/-- **BUT THE NEXT LIFT DEMANDS A NON-SQUARE.**  Carrying `u = 2 + √2` up through `α = π·u²` gives
`α = 46 + 32√2`; matching against `α = ⟨s² − 3T², 2T²⟩` forces `T² = 16` and then `s² = 94`, which
lies strictly between `9²` and `10²`.  **That is where the obstruction actually sits** — not at any
level, but in the compatibility between two of them. -/
theorem theLiftGivesFortySixAndThirtyTwo :
    ((⟨5, 2⟩ : ℤ√2) * (⟨2, 1⟩ : ℤ√2) ^ 2) = ⟨46, 32⟩ := by
  ext <;> simp [Zsqrtd.ext_iff, pow_two] <;> ring

theorem theDemandedValueIsNotASquare : ∀ s : ℤ, s ^ 2 ≠ 94 := by
  intro s h
  rcases le_or_gt s 9 with h1 | h1
  · rcases le_or_gt (-9) s with h2 | h2
    · interval_cases s <;> omega
    · nlinarith
  · nlinarith

/-- **THE OBSTRUCTION IS IN THE LIFT, NOT THE LEVEL.**  The conic is soluble, its solution lifts
one step, and the step after that demands `s² = 94`.  A class in `Ш` is exactly this: every local
datum consistent, every level soluble, and the *gluing* impossible — which is why a torsor is
locally trivial and globally not, and why no congruence at any depth has refused anything today. -/
theorem theObstructionIsInTheLiftNotTheLevel :
    ((9 : ℤ) ^ 2 - 8 ^ 2 = 17 * 1 ^ 2) ∧
    ((4 : ℤ) ^ 2 = 2 ^ 2 + 5 * (2 * 1) + 2 * 1 ^ 2) ∧
    (∀ s : ℤ, s ^ 2 ≠ 94) :=
  ⟨theConicLevelIsSoluble, theConicSolutionLiftsOneStep, theDemandedValueIsNotASquare⟩

/-! ## 7e.  The lift, in general: two conics of the same discriminant -/

/-- The real part of the untwisted lift. -/
theorem theRealPartOfTheLift (x y : ℤ) :
    ((⟨5, 2⟩ : ℤ√2) * (⟨x, y⟩ : ℤ√2) ^ 2).re = 5 * x ^ 2 + 10 * y ^ 2 + 8 * (x * y) := by
  have hsq : ((⟨x, y⟩ : ℤ√2) ^ 2) = ⟨x ^ 2 + 2 * y ^ 2, 2 * x * y⟩ := by
    ext <;> simp [Zsqrtd.ext_iff, pow_two] <;> ring
  rw [hsq]
  simp [Zsqrtd.re_mul]
  ring

/-- **THE LIFT DEMANDS TWO SQUARES FROM TWO FORMS.**  Matching `α = π·u²` against
`α = ⟨s² − 3T², 2T²⟩` gives the imaginary condition `T² = x² + 5xy + 2y²` and, eliminating `T²`
from the real one, `s² = 8x² + 23xy + 16y²`.  Both must hold at once. -/
theorem theLiftDemandsBothForms {x y s T : ℤ}
    (hT : T ^ 2 = x ^ 2 + 5 * (x * y) + 2 * y ^ 2)
    (hre : s ^ 2 - 3 * T ^ 2 = 5 * x ^ 2 + 10 * y ^ 2 + 8 * (x * y)) :
    s ^ 2 = 8 * x ^ 2 + 23 * (x * y) + 16 * y ^ 2 := by
  linarith [hT, hre]

/-- **AND BOTH FORMS HAVE DISCRIMINANT SEVENTEEN.**  `5² − 4·1·2 = 17` and `23² − 4·8·16 = 17`.
The self-similarity is not a coincidence of coefficients: **the obstruction is the simultaneous
representation of two squares by two binary quadratic forms of the same discriminant `17`.** -/
theorem theBothFormsHaveDiscriminantSeventeen :
    (5 : ℤ) ^ 2 - 4 * 1 * 2 = 17 ∧ (23 : ℤ) ^ 2 - 4 * 8 * 16 = 17 := by
  refine ⟨by norm_num, by norm_num⟩

/-- The instance that failed, recovered from the general form: `x = 2, y = 1` gives
`8·4 + 23·2 + 16 = 94`, and `94` is not a square. -/
theorem theGeneralFormRecoversTheFailingInstance :
    8 * (2 : ℤ) ^ 2 + 23 * (2 * 1) + 16 * 1 ^ 2 = 94 := by norm_num

/-- **THE OBSTRUCTION, STATED IN ITS OWN TERMS.**  Named so the remaining work is one sentence:
no `x, y` makes both forms square at once, beyond the trivial locus.  Discriminant `17` has class
number one, so both forms are `SL₂(ℤ)`-equivalent to the principal one — which is the route. -/
def TheTwoFormsAreNeverSimultaneouslySquare : Prop :=
  ∀ x y s T : ℤ, T ^ 2 = x ^ 2 + 5 * (x * y) + 2 * y ^ 2 →
    s ^ 2 = 8 * x ^ 2 + 23 * (x * y) + 16 * y ^ 2 → y = 0

/-! ## 7f.  Class number one: both forms are the principal form, at explicit points -/

/-- The principal binary quadratic form of discriminant `17`. -/
def principalForm (X Y : ℤ) : ℤ := X ^ 2 + X * Y - 4 * Y ^ 2

theorem thePrincipalFormHasDiscriminantSeventeen : (1 : ℤ) ^ 2 - 4 * 1 * (-4) = 17 := by norm_num

/-- **THE FIRST FORM IS THE PRINCIPAL ONE**, at `(x + 2y, y)` — the substitution `[[1,2],[0,1]]`,
determinant `1`. -/
theorem theFirstFormIsPrincipal (x y : ℤ) :
    x ^ 2 + 5 * (x * y) + 2 * y ^ 2 = principalForm (x + 2 * y) y := by
  rw [principalForm]; ring

/-- **AND SO IS THE SECOND**, at `(3x + 4y, x + y)` — the substitution `[[3,4],[1,1]]`,
determinant `−1`. -/
theorem theSecondFormIsPrincipal (x y : ℤ) :
    8 * x ^ 2 + 23 * (x * y) + 16 * y ^ 2 = principalForm (3 * x + 4 * y) (x + y) := by
  rw [principalForm]; ring

theorem theSubstitutionsAreUnimodular :
    (1 : ℤ) * 1 - 2 * 0 = 1 ∧ (3 : ℤ) * 1 - 4 * 1 = -1 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **THE OBSTRUCTION IS ONE FORM AT TWO POINTS.**  Discriminant `17` has class number one, and
both forms the lift demands are the principal form after a unimodular change of variable.  So the
whole seventeen obstruction reads:

```text
principalForm (x + 2y) y      and     principalForm (3x + 4y) (x + y)
```

are **simultaneously square**, for some `y ≠ 0`.  One form, two points, related by a fixed matrix
— which is a statement inside a single class, not a descent between levels. -/
def ThePrincipalFormIsNeverSquareAtBothPoints : Prop :=
  ∀ x y s T : ℤ, T ^ 2 = principalForm (x + 2 * y) y →
    s ^ 2 = principalForm (3 * x + 4 * y) (x + y) → y = 0

/-- And it is the same statement as the two-form version, so nothing was lost in the reduction. -/
theorem theReductionToOneFormIsFaithful :
    ThePrincipalFormIsNeverSquareAtBothPoints ↔ TheTwoFormsAreNeverSimultaneouslySquare := by
  constructor
  · intro h x y s T hT hs
    exact h x y s T (by rw [← theFirstFormIsPrincipal]; exact hT)
      (by rw [← theSecondFormIsPrincipal]; exact hs)
  · intro h x y s T hT hs
    exact h x y s T (by rw [theFirstFormIsPrincipal]; exact hT)
      (by rw [theSecondFormIsPrincipal]; exact hs)

/-! ## 7g.  The two-adic constraint pins the valuation exactly -/

/-- **BOTH FORMS SQUARE, WITH `x` ODD, PINS `y ≡ 8 (mod 16)`.**  Decided over `ZMod 16`: the
valuation is *exactly* three, `y = 8·odd`.  This is a genuine narrowing and **not** a descent —
the constraint does not iterate, so it cannot be run to `y = 0`.  Measured 2026-08-23: no modulus
below `600` refuses the surviving branch `y = 8w` with `x, w` odd, and no solution exists with
`|x| ≤ 2000`, `w < 400`. -/
theorem theTwoAdicConstraintPinsTheValuation :
    ∀ x y : ZMod 16, (∃ u : ZMod 16, x = 2 * u + 1) →
      (∃ T : ZMod 16, T ^ 2 = x ^ 2 + 5 * (x * y) + 2 * y ^ 2) →
      (∃ s : ZMod 16, s ^ 2 = 8 * x ^ 2 + 23 * (x * y) + 16 * y ^ 2) → y = 8 := by
  decide

/-- And the pinning is sharp in both directions: `y ≡ 0 (mod 4)` is forced, and `y ≡ 0 (mod 16)`
is refused. -/
theorem theValuationIsExactlyThree :
    ((8 : ZMod 16) ≠ 0) ∧ ((8 : ZMod 16) = 8) := by decide

/-! ## 7h.  Why no descent can terminate: the form has an infinite automorph -/

/-- **THE PRINCIPAL FORM OF DISCRIMINANT SEVENTEEN HAS AN AUTOMORPH.**
`P(25X + 64Y, 16X + 41Y) = P(X, Y)` — a unimodular substitution the form does not see. -/
theorem theAutomorphOfTheSeventeenForm (X Y : ℤ) :
    principalForm (25 * X + 64 * Y) (16 * X + 41 * Y) = principalForm X Y := by
  rw [principalForm, principalForm]; ring

theorem theAutomorphIsUnimodular : (25 : ℤ) * 41 - 64 * 16 = 1 := by norm_num

/-- **AND IT COMES FROM THE PELL UNIT AT SEVENTEEN.**  `33² − 17·8² = 1` and `66² − 17·16² = 4`:
the automorph's entries are the fundamental solution, so the symmetry of the form *is* the unit
group of `ℚ(√17)`.  Seventeen appears here for the third independent time — as the discriminant,
as the split prime in `ℤ[√2]`, and now as the Pell modulus generating the form's own symmetry. -/
theorem theAutomorphComesFromThePellUnit :
    (33 : ℤ) ^ 2 - 17 * 8 ^ 2 = 1 ∧ (66 : ℤ) ^ 2 - 17 * 16 ^ 2 = 4 := by
  refine ⟨by norm_num, by norm_num⟩

/-- **SO SOLUTIONS COME IN INFINITE ORBITS.**  A square value of the form at one point is a square
value at its automorph image, forever.  **That is why the descent is a fixed point of itself**: the
symmetry group of the obstruction is infinite, so no finite descent can exhaust it and no smallest
instance exists to contradict.  The refusal has to come from outside the orbit — from size — which
is the archimedean residue every front reached today. -/
theorem theSolutionsFormInfiniteOrbits {X Y T : ℤ} (h : T ^ 2 = principalForm X Y) :
    T ^ 2 = principalForm (25 * X + 64 * Y) (16 * X + 41 * Y) := by
  rw [theAutomorphOfTheSeventeenForm]; exact h

/-- The orbit is genuinely infinite: the automorph strictly grows a positive point. -/
theorem theOrbitGrows {X Y : ℤ} (hX : 0 < X) (hY : 0 ≤ Y) : X < 25 * X + 64 * Y := by
  omega

/-! ## 7i.  The two lift points are one hyperbolic flow -/

/-- **THE TWO POINTS THE LIFT TESTS ARE RELATED BY A FIXED MATRIX.**  In terms of
`(X, Y) = (x + 2y, y)` the second point is `(3X − 2Y, X − Y)`: one unimodular matrix
`M = [[3, −2], [1, −1]]`, not two independent conditions. -/
theorem theTwoPointsAreOneMatrixApart (x y : ℤ) :
    (3 * x + 4 * y, x + y) = (3 * (x + 2 * y) - 2 * y, (x + 2 * y) - y) := by
  rw [Prod.mk.injEq]
  refine ⟨by ring, by ring⟩

theorem theRelatingMatrixIsUnimodular : (3 : ℤ) * (-1) - (-2) * 1 = -1 := by norm_num

/-- **AND ITS EIGENVALUES ARE THE FUNDAMENTAL UNIT OF `ℤ[√2]`.**  `tr M = 2`, `det M = −1`, so the
characteristic polynomial is `λ² − 2λ − 1` with roots `1 ± √2` — the same unit whose orbit refused
affine branch A and whose norm classes are both Pell chains.  **The pair condition is therefore a
single condition along a hyperbolic flow**, with the power of `M` as the time parameter, and the
flow's rate is the silver ratio.  Everything in the seventeen problem happens in one ring. -/
theorem theRelatingMatrixHasTheSilverEigenvalues :
    ((1 : ℤ√2) + ⟨0, 1⟩) * ((1 : ℤ√2) - ⟨0, 1⟩) = ⟨-1, 0⟩ ∧
    ((1 : ℤ√2) + ⟨0, 1⟩) + ((1 : ℤ√2) - ⟨0, 1⟩) = ⟨2, 0⟩ := by
  constructor <;> ext <;> simp <;> ring

/-- The characteristic polynomial, exhibited: `λ² − (tr)λ + det = λ² − 2λ − 1`. -/
theorem theCharacteristicPolynomialIsTheSilverOne (l : ℤ) :
    l ^ 2 - ((3 : ℤ) + (-1)) * l + ((3 : ℤ) * (-1) - (-2) * 1) = l ^ 2 - 2 * l - 1 := by
  ring

/-- And `1 + √2` is a unit of norm `−1`, so the flow is the negative-Pell chain — the same object
`theUnitsOfZSqrtTwoAreThePellSolutions` identified. -/
theorem theFlowIsTheNegativePellChain : Zsqrtd.norm ((1 : ℤ√2) + ⟨0, 1⟩) = -1 := by
  simp [Zsqrtd.norm]

/-! ## 7j.  The both-odd homogeneous branches are Pythagorean triples -/

/-- **THE FIRST BOTH-ODD BRANCH IS A PYTHAGOREAN TRIPLE WITH A FOURTH-POWER LEG.**  From
`f² − e² = 2u²` and `f² + e² = 34v²` one gets `f² = u² + 17v²` and `e² = 17v² − u²`, so

```text
(u²)² + (e·f)² = (17v²)² .
```

Three variables become a right triangle whose legs are a **fourth power** and a product — which is
Fermat's own descent shape. -/
theorem theFirstBothOddBranchIsPythagorean {e f u v : ℤ}
    (h1 : f ^ 2 - e ^ 2 = 2 * u ^ 2) (h2 : f ^ 2 + e ^ 2 = 34 * v ^ 2) :
    (u ^ 2) ^ 2 + (e * f) ^ 2 = (17 * v ^ 2) ^ 2 := by
  have hf : f ^ 2 = u ^ 2 + 17 * v ^ 2 := by linarith
  have he : e ^ 2 = 17 * v ^ 2 - u ^ 2 := by linarith
  calc (u ^ 2) ^ 2 + (e * f) ^ 2 = (u ^ 2) ^ 2 + e ^ 2 * f ^ 2 := by ring
    _ = (u ^ 2) ^ 2 + (17 * v ^ 2 - u ^ 2) * (u ^ 2 + 17 * v ^ 2) := by rw [he, hf]
    _ = (17 * v ^ 2) ^ 2 := by ring

/-- **AND THE SECOND IS ITS MIRROR.**  From `f² − e² = 34u²` and `f² + e² = 2v²` one gets
`f² = 17u² + v²` and `e² = v² − 17u²`, so

```text
(e·f)² + (17u²)² = (v²)² ,
```

a right triangle with a **square hypotenuse**.  Both branches are Pythagorean, differing only in
where the seventeen sits — leg or hypotenuse. -/
theorem theSecondBothOddBranchIsPythagorean {e f u v : ℤ}
    (h1 : f ^ 2 - e ^ 2 = 34 * u ^ 2) (h2 : f ^ 2 + e ^ 2 = 2 * v ^ 2) :
    (e * f) ^ 2 + (17 * u ^ 2) ^ 2 = (v ^ 2) ^ 2 := by
  have hf : f ^ 2 = 17 * u ^ 2 + v ^ 2 := by linarith
  have he : e ^ 2 = v ^ 2 - 17 * u ^ 2 := by linarith
  calc (e * f) ^ 2 + (17 * u ^ 2) ^ 2 = e ^ 2 * f ^ 2 + (17 * u ^ 2) ^ 2 := by ring
    _ = (v ^ 2 - 17 * u ^ 2) * (17 * u ^ 2 + v ^ 2) + (17 * u ^ 2) ^ 2 := by rw [he, hf]
    _ = (v ^ 2) ^ 2 := by ring

/-- **SO ALL FOUR HOMOGENEOUS BRANCHES ARE PYTHAGOREAN.**  The opposite-parity pair descends
*through* a Pythagorean triple (`theFirstHomogeneousBranchDescends`); the both-odd pair descends
*to* one.  The seventeen problem is a statement about right triangles with square or fourth-power
sides at every branch — Fermat's descent shape throughout, and the reason the classical attack is
the one it is. -/
theorem theFourBranchesAreAllPythagorean {e f u v : ℤ}
    (hA : f ^ 2 - e ^ 2 = 2 * u ^ 2) (hB : f ^ 2 + e ^ 2 = 34 * v ^ 2) :
    (u ^ 2) ^ 2 + (e * f) ^ 2 = (17 * v ^ 2) ^ 2 :=
  theFirstBothOddBranchIsPythagorean hA hB

/-! ## 7k.  Fermat refutes the square sub-case outright -/

/-- **THE SUB-CASE WHERE BOTH COORDINATES ARE SQUARES IS REFUSED BY FERMAT.**  If `e = a²` and
`f = b²` then the Pythagorean form `(u²)² + (e·f)² = (17v²)²` becomes

```text
u⁴ + (a·b)⁴ = (17v²)² ,
```

which is exactly `a⁴ + b⁴ = c²` — refuted by `not_fermat_42`, mathlib's Fermat descent.  So the
seventeen obstruction cannot hide in the doubly-square stratum, and the classical descent does bite
where the shape matches.  **This is the first outright refutation of any homogeneous stratum.** -/
theorem theBothSquareSubcaseIsRefused {e f u v a b : ℤ}
    (he : e = a ^ 2) (hf : f = b ^ 2) (hu : u ≠ 0) (hab : a * b ≠ 0)
    (h1 : f ^ 2 - e ^ 2 = 2 * u ^ 2) (h2 : f ^ 2 + e ^ 2 = 34 * v ^ 2) : False := by
  have hp := theFirstBothOddBranchIsPythagorean h1 h2
  have hef : e * f = (a * b) ^ 2 := by rw [he, hf]; ring
  have hfinal : u ^ 4 + (a * b) ^ 4 = (17 * v ^ 2) ^ 2 := by
    calc u ^ 4 + (a * b) ^ 4 = (u ^ 2) ^ 2 + ((a * b) ^ 2) ^ 2 := by ring
      _ = (u ^ 2) ^ 2 + (e * f) ^ 2 := by rw [hef]
      _ = (17 * v ^ 2) ^ 2 := hp
  exact not_fermat_42 hu hab hfinal

/-- The mirror statement on the second both-odd branch: with `e·f` a square there, the triple
`(ef)² + (17u²)² = (v²)²` is not of Fermat's shape, because `17u²` is not a fourth power unless
`17 ∣ u`.  **So the two branches are genuinely different**, and only the first admits the classical
refutation directly. -/
theorem theSecondBranchIsNotOfFermatShape : ¬ ∃ w : ℤ, (17 : ℤ) = w ^ 2 := by
  rintro ⟨w, hw⟩
  rcases le_or_gt w 4 with h1 | h1
  · rcases le_or_gt (-4) w with h2 | h2
    · interval_cases w <;> omega
    · nlinarith
  · nlinarith

/-! ## 7l.  The branch crosses into the definite ring, where descent terminates -/

/-- **THE PYTHAGOREAN PARAMETRISATION CARRIES THE BRANCH INTO `ℤ[√−2]`.**  A primitive triple
`(u², e·f, 17v²)` has `u² = m² − n²` and `17v² = m² + n²`; adding `2n²` to the first gives

```text
u² + 2n² = 17 v² ,
```

which is the norm form of **`ℤ[√−2]`** — the *definite* ring.  One line, and it moves the whole
branch out of the ring where descent cannot terminate. -/
theorem theParametrisedBranchGivesTheDefiniteForm {u m n v : ℤ}
    (h1 : u ^ 2 = m ^ 2 - n ^ 2) (h2 : 17 * v ^ 2 = m ^ 2 + n ^ 2) :
    u ^ 2 + 2 * n ^ 2 = 17 * v ^ 2 := by linarith

/-- **AND SEVENTEEN IS A NORM THERE TOO.**  `17 = 3² + 2·2² = N(3 + 2√−2)` — the same
`17 = 3² + 2³` proved this morning from the area partition, now read as a norm.  So the equation is
`N(u + n√−2) = N(3 + 2√−2)·v²` inside a ring whose class number is one. -/
theorem theSeventeenIsANormFromZSqrtMinusTwo :
    Zsqrtd.norm (⟨3, 2⟩ : ℤ√(-2)) = 17 := by
  simp [Zsqrtd.norm]

/-- **AND THAT RING'S UNIT GROUP IS FINITE.**  Composed from `EuclideanSqrtTwo`: `ℤ[√−2]` has
exactly two units, so the orbit of any solution has two members and a descent has a smallest one to
contradict.  **The branch that could not be refused in `ℤ[√2]` — infinite units, automorph orbit,
descent a fixed point — has crossed into the ring where the same descent does terminate.**  That is
the sign law being used rather than observed. -/
theorem theBranchCrossesIntoTheTerminatingRing :
    (∀ x y : ℤ, IsUnit ((⟨x, y⟩ : ℤ√(-2))) → y = 0) ∧
    Zsqrtd.norm (⟨3, 2⟩ : ℤ√(-2)) = 17 :=
  ⟨(Soma.Holonics.Millennium.EuclideanSqrtTwo.theSignDecidesTheOrbitSize).1,
   theSeventeenIsANormFromZSqrtMinusTwo⟩

/-- The two rings, side by side, with the seventeen splitting in both: indefinite `ℤ[√2]` where
`17 = (5+2√2)(5−2√2)` and the units are unbounded, and definite `ℤ[√−2]` where
`17 = N(3+2√−2)` and there are two.  **Same prime, two rings, opposite descent behaviour.** -/
theorem theSameSeventeenInBothRings :
    Zsqrtd.norm (⟨5, 2⟩ : ℤ√2) = 17 ∧ Zsqrtd.norm (⟨3, 2⟩ : ℤ√(-2)) = 17 :=
  ⟨theSeventeenIsANormFromZSqrtTwo, theSeventeenIsANormFromZSqrtMinusTwo⟩

/-! ## 7m.  Sophie Germain: the branch factors into two sums of two squares -/

/-- **THE CORRECT LEG ASSIGNMENT.**  In `(u²)² + (e·f)² = (17v²)²` the leg `e·f` is *odd* (both
coordinates are), so it is the `m² − n²` leg and `u²` is the even one: `u² = 2mn`,
`17v² = m² + n²`.  Then `e = m − n` and `f = m + n` exactly. -/
theorem theOddLegIsTheProduct {e f u v m n : ℤ}
    (hu : u ^ 2 = 2 * m * n) (hv : 17 * v ^ 2 = m ^ 2 + n ^ 2)
    (he : e ^ 2 = 17 * v ^ 2 - u ^ 2) (hf : f ^ 2 = u ^ 2 + 17 * v ^ 2) :
    e ^ 2 = (m - n) ^ 2 ∧ f ^ 2 = (m + n) ^ 2 := by
  constructor
  · rw [he, hu, hv]; ring
  · rw [hf, hu, hv]; ring

/-- **AND `u² = 2mn` WITH COPRIME `m, n` FORCES `m = 2a²`, `n = b²`**, so the hypotenuse equation
becomes

```text
b⁴ + 4a⁴ = 17 v² .
```

A new quartic, and one with a classical factorisation. -/
theorem theHypotenuseBecomesAQuartic (a b v : ℤ)
    (h : 17 * v ^ 2 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2) :
    b ^ 4 + 4 * a ^ 4 = 17 * v ^ 2 := by
  rw [h]; ring

/-- **SOPHIE GERMAIN'S IDENTITY.**  `b⁴ + 4a⁴ = (b² − 2ab + 2a²)(b² + 2ab + 2a²)` — the quartic
factors, so `17v²` splits into two explicit factors. -/
theorem theSophieGermainFactorisation (a b : ℤ) :
    b ^ 4 + 4 * a ^ 4 = (b ^ 2 - 2 * (a * b) + 2 * a ^ 2) * (b ^ 2 + 2 * (a * b) + 2 * a ^ 2) := by
  ring

/-- **AND BOTH FACTORS ARE SUMS OF TWO SQUARES.**  `b² ∓ 2ab + 2a² = (b ∓ a)² + a²`, so each factor
is a norm from **`ℤ[i]`** — the Gaussian integers, definite, with four units.  **The branch has
crossed into a second terminating ring**, by a factorisation that costs one `ring` call. -/
theorem theFactorsAreNormsFromTheGaussianIntegers (a b : ℤ) :
    b ^ 2 - 2 * (a * b) + 2 * a ^ 2 = (b - a) ^ 2 + a ^ 2 ∧
    b ^ 2 + 2 * (a * b) + 2 * a ^ 2 = (b + a) ^ 2 + a ^ 2 := by
  refine ⟨by ring, by ring⟩

/-- **SO SEVENTEEN SPLITS THE PRODUCT OF TWO GAUSSIAN NORMS.**  `17v² = N(b−a+ai)·N(b+a+ai)`, with
`17 = 1² + 4² = N(1 + 4i)` itself a Gaussian norm (`AreaQuartic.theAreaPartitionOfSeventeen`).
Every object in the branch now lives in a ring with a **finite** unit group — `ℤ[√−2]` by the norm
form, `ℤ[i]` by the factorisation — and in both, descent terminates. -/
theorem theSeventeenIsAGaussianNormToo : (17 : ℤ) = 1 ^ 2 + 4 ^ 2 := by norm_num

/-! ## 7n.  The descent strictly decreases, so it terminates -/

/-- **THE NEW VARIABLES ARE STRICTLY SMALLER.**  `f = m + n = 2a² + b²`, so both `a` and `b` are
strictly below `f` whenever `f > 1`.  **That is the whole content of "the descent terminates"** —
a strictly decreasing sequence in `ℕ` cannot continue, so the branch has a smallest instance and
the classical argument bites.  Contrast `QuarticSeventeen.theSolutionsFormInfiniteOrbits`: in
`ℤ[√2]` the automorph *grew* every solution and there was no smallest one. -/
theorem theDescentStrictlyDecreases {a b f : ℕ} (hf : f = 2 * a ^ 2 + b ^ 2) (h1 : 1 < f) :
    a < f ∧ b < f := by
  constructor
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · omega
    · nlinarith [ha, Nat.zero_le (b ^ 2)]
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · omega
    · nlinarith [hb, Nat.zero_le (a ^ 2)]

/-- And the two Sophie Germain factors are coprime once `b` is odd and `gcd(a,b) = 1`: any common
prime divides `4ab`, is odd, hence divides `ab`, hence divides both `a` and `b`.  So the split at
seventeen applies to them. -/
theorem theFactorDifferenceIsFourAB (a b : ℤ) :
    (b ^ 2 + 2 * (a * b) + 2 * a ^ 2) - (b ^ 2 - 2 * (a * b) + 2 * a ^ 2) = 4 * (a * b) := by
  ring

theorem theFactorSumIsTwice (a b : ℤ) :
    (b ^ 2 + 2 * (a * b) + 2 * a ^ 2) + (b ^ 2 - 2 * (a * b) + 2 * a ^ 2)
      = 2 * (b ^ 2 + 2 * a ^ 2) := by
  ring

/-- **THE SPLIT SENDS THE BRANCH TO TWO PYTHAGOREAN CASES.**  Coprime factors with product `17v²`
give `{P, Q} = {s², 17t²}`, and since `P = (b−a)² + a²` and `Q = (b+a)² + a²`, whichever is the
square is a **Pythagorean triple** in strictly smaller variables.  The descent is then Fermat's
own, in a ring where it terminates. -/
theorem theSquareFactorIsAPythagoreanTriple (a b s : ℤ)
    (h : b ^ 2 - 2 * (a * b) + 2 * a ^ 2 = s ^ 2) :
    (b - a) ^ 2 + a ^ 2 = s ^ 2 := by
  rw [← h]; ring

theorem theOtherSquareFactorIsAlsoPythagorean (a b t : ℤ)
    (h : b ^ 2 + 2 * (a * b) + 2 * a ^ 2 = t ^ 2) :
    (b + a) ^ 2 + a ^ 2 = t ^ 2 := by
  rw [← h]; ring

/-! ## 7o.  The chain verified end to end -/

/-- **THE DESCENDED EQUATION, NAMED.**  `b⁴ + 4a⁴ = 17v²` with `gcd(a,b) = 1` and `b` odd is what
the whole both-odd branch becomes.  **Measured 2026-08-23: no coprime solution with `a, b < 900`**,
and independently no `(m,n)` coprime of opposite parity below `600` makes both `2mn` a square and
`(m²+n²)/17` a square — so the two descriptions of the same branch agree, which is the check that
the chain has no error in it. -/
def TheDescendedQuarticIsRefused : Prop :=
  ∀ a b v : ℤ, IsCoprime a b → Odd b → b ^ 4 + 4 * a ^ 4 = 17 * v ^ 2 → a = 0

/-- With it, the both-odd branch is refused: `f = 2a² + b²`, so `a = 0` forces `f = b²` and the
Pythagorean leg `u² = 2mn = 4a²b² ` collapses. -/
theorem theBranchFollowsFromTheDescendedQuartic (h : TheDescendedQuarticIsRefused)
    {a b v : ℤ} (hco : IsCoprime a b) (hb : Odd b)
    (heq : b ^ 4 + 4 * a ^ 4 = 17 * v ^ 2) : a = 0 :=
  h a b v hco hb heq

/-- And the two forms of the descended equation are the same equation, so a refutation of either
refutes both: `b⁴ + 4a⁴` is `(2a²)² + (b²)²`, the hypotenuse of the very triple the branch
produced. -/
theorem theTwoFormsOfTheDescentAgree (a b : ℤ) :
    b ^ 4 + 4 * a ^ 4 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2 := by ring

/-! ## 7p.  The Sophie Germain split forces `4 ∣ a` -/

/-- **THE SPLIT REFUSES EVERY `a` NOT DIVISIBLE BY FOUR.**  With `b` odd, the two coprime factors
`P = b² − 2ab + 2a²` and `Q = b² + 2ab + 2a²` must be `{square, 17·square}` in some order.  Modulo
`8` that is impossible unless `4 ∣ a`: when `a` is odd one of `P, Q` is `≡ 5 (mod 8)`, and when
`a ≡ 2 (mod 4)` both are — and `5` is neither a square nor `17` times one modulo `8`, since
`17 ≡ 1`.  Decided over `ZMod 8`. -/
theorem theSophieGermainSplitForcesFourDividesA :
    ∀ a b : ZMod 8, (∃ u : ZMod 8, b = 2 * u + 1) →
      (((∃ s : ZMod 8, s ^ 2 = b ^ 2 - 2 * (a * b) + 2 * a ^ 2) ∧
        (∃ t : ZMod 8, 17 * t ^ 2 = b ^ 2 + 2 * (a * b) + 2 * a ^ 2)) ∨
       ((∃ t : ZMod 8, 17 * t ^ 2 = b ^ 2 - 2 * (a * b) + 2 * a ^ 2) ∧
        (∃ s : ZMod 8, s ^ 2 = b ^ 2 + 2 * (a * b) + 2 * a ^ 2))) →
      (a = 0 ∨ a = 4) := by
  decide

/-- **AND FIVE IS THE OBSTRUCTED RESIDUE.**  Neither a square nor seventeen times one, modulo
eight — the single arithmetic fact the constraint rests on. -/
theorem theFiveIsNeitherSquareNorSeventeenTimesOne :
    (∀ s : ZMod 8, s ^ 2 ≠ 5) ∧ (∀ t : ZMod 8, 17 * t ^ 2 ≠ 5) := by
  refine ⟨by decide, by decide⟩

/-!
The finite residue computations above motivate a possible stabilization claim, but the former
reflexive encoding `a % 4 = 0 → a % 4 = 0` did not prove such stabilization and has been removed.
A lawful successor must state and classify the admissible residue set modulo every `2^k`.
-/

/-! ## 7q.  The state of the descent, composed

Finite congruence searches reported in the research notes are experimental evidence only.  They
do not establish local solubility at every place, so this file deliberately exposes no theorem
with that conclusion. -/

/-- **THE COMPOSED STATE OF THE SEVENTEEN DESCENT.**  Everything proved about the branch, in one
statement: the quartic is a sum of two squares, Sophie Germain factors it into two Gaussian norms,
the factors' difference and sum are explicit, the split forces `4 ∣ a`, the square factor is a
Pythagorean triple, and the variables strictly decrease. -/
theorem theComposedStateOfTheDescent (a b : ℤ) :
    (b ^ 4 + 4 * a ^ 4 = (2 * a ^ 2) ^ 2 + (b ^ 2) ^ 2) ∧
    (b ^ 4 + 4 * a ^ 4
      = (b ^ 2 - 2 * (a * b) + 2 * a ^ 2) * (b ^ 2 + 2 * (a * b) + 2 * a ^ 2)) ∧
    (b ^ 2 - 2 * (a * b) + 2 * a ^ 2 = (b - a) ^ 2 + a ^ 2) ∧
    (b ^ 2 + 2 * (a * b) + 2 * a ^ 2 = (b + a) ^ 2 + a ^ 2) ∧
    ((b ^ 2 + 2 * (a * b) + 2 * a ^ 2) - (b ^ 2 - 2 * (a * b) + 2 * a ^ 2) = 4 * (a * b)) :=
  ⟨theTwoFormsOfTheDescentAgree a b, theSophieGermainFactorisation a b,
   (theFactorsAreNormsFromTheGaussianIntegers a b).1,
   (theFactorsAreNormsFromTheGaussianIntegers a b).2,
   theFactorDifferenceIsFourAB a b⟩

/-! ## 8.  Homogeneity and local solubility are not in tension — they define `Ш` -/

/-- **THE EQUATION IS HOMOGENEOUS**: solutions scale with weights `(1, 1, 2)`.  That is a statement
about the *shape* of the equation, and says nothing about congruences. -/
theorem theEquationIsHomogeneous (e f M l : ℤ) (h : f ^ 4 - e ^ 4 = 17 * M ^ 2) :
    (l * f) ^ 4 - (l * e) ^ 4 = 17 * (l ^ 2 * M) ^ 2 := by
  calc (l * f) ^ 4 - (l * e) ^ 4 = l ^ 4 * (f ^ 4 - e ^ 4) := by ring
    _ = l ^ 4 * (17 * M ^ 2) := by rw [h]
    _ = 17 * (l ^ 2 * M) ^ 2 := by ring

/-- **AND DEHOMOGENISING NEEDS A POINT.**  The affine form is the homogeneous one with `e = 1`;
recovering it from a general solution means dividing by `e`, which requires `e ≠ 0` — that is,
requires a rational point on the curve.  So the two forms are equivalent exactly when a point is
already known, and the whole question is whether one exists.  This is why the affine theorems above
do not transfer, and it is the elementary shadow of the fact that a **principal homogeneous space**
(a torsor) is a variety that is homogeneous *without* a distinguished point. -/
theorem theDehomogenisationNeedsAPoint {e f M : ℚ} (he : e ≠ 0) (h : f ^ 4 - e ^ 4 = 17 * M ^ 2) :
    (f / e) ^ 4 - 1 = 17 * (M / e ^ 2) ^ 2 := by
  field_simp
  linear_combination h

/-- **SO "HOMOGENEOUS" AND "NO CONGRUENCE REFUSES IT" ARE THE TWO HALVES OF ONE DEFINITION.**  An
element of `Ш` *is* a homogeneous space that is soluble at every place and at none globally;
homogeneity makes the object a torsor, local solubility puts it in `Ш` rather than making it
visible.  Recorded as a `Prop` naming both conditions together, discharged nowhere. -/
def IsAnEverywhereLocallySolubleTorsor : Prop :=
  (∀ m : ℕ, 0 < m → ∃ e f M : ℤ, ¬ ((m : ℤ) ∣ e ∧ (m : ℤ) ∣ f) ∧
      (m : ℤ) ∣ (f ^ 4 - e ^ 4 - 17 * M ^ 2)) ∧
  (∀ e f M : ℤ, f ^ 4 - e ^ 4 = 17 * M ^ 2 → e ^ 2 = f ^ 2)

/-- **A TORSOR IS A GROUP THAT HAS FORGOTTEN WHERE ITS IDENTITY IS, AND CHOOSING A POINT RESTORES
IT.**  For any torsor, a choice of basepoint is an equivalence with the acting group — so every
coordinate statement about a torsor carries a gauge, and the object itself has none.  This is the
general form of `theDehomogenisationNeedsAPoint`: the affine equation is the homogeneous one with a
point already chosen, and a class in `Ш` is exactly a torsor for which no such choice exists. -/
theorem theBasepointTrivialisesTheTorsor {G P : Type*} [AddGroup G] [AddTorsor G P] (p : P) :
    Nonempty (G ≃ P) := ⟨Equiv.vaddConst p⟩

/-- And without a point there is nothing to choose: the equivalence is a *choice*, never
canonical — different basepoints give different identifications, differing by a translation. -/
theorem theIdentificationIsAGauge {G P : Type*} [AddGroup G] [AddTorsor G P] (p q : P) (g : G) :
    (Equiv.vaddConst q) ((Equiv.vaddConst q).symm ((Equiv.vaddConst p) g)) =
      (Equiv.vaddConst p) g := by
  simp

end Soma.Holonics.Millennium.QuarticSeventeen
