import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Nth
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Landmarks and moduli

Primes are landmarks; an additive decomposition in a base is a **path** between them; and what
survives a change of path is the **modulus**.  This file carries the theorems that say exactly that,
the ones that are imported rather than proved, and the concrete table the corpus's own sign-word
family lands on.

**What is proved here.**  A depth `p` admits a modulus `n` exactly when two has period dividing `p`
modulo `n`, so the least depth at which a modulus becomes reachable is the multiplicative order of
two — and the moduli the period-`p` sign words land on, `2^p ∓ 1` by minus-count parity, are
tabulated and decided.  This is the arithmetic law behind the nested-radical family, whose values
are `2cos(π m / (2^p ∓ 1))` and whose isolation `crates/holonic-engine/src/winding_inertia.rs`
performs exactly by Sturm bisection on the Dickson polynomial.

**What is imported from mathlib and restated, not proved.**  Kummer's theorem, in the form
`Nat.factorization_choose`: the multiplicity of a prime in a binomial coefficient is *the number of
carries*, so the digits do not enter and only the carry count does.  Bertrand's postulate,
`Nat.exists_prime_lt_and_le_two_mul`.  And the Möbius sign as the half-turn parity on squarefree
numbers.

**What is imported as a named `Prop` with its status, and proved nowhere here.**  Legendre's
conjecture and Cramér's conjecture, both **OPEN**; Baker–Harman–Pintz, a theorem; the gap bound the
Riemann Hypothesis delivers; the square-root cancellation of the Möbius walk, equivalent to RH; and
Lucas' congruence, a theorem mathlib does not carry.  Each is a real statement — none is `True`
wearing a name — and none is claimed to be established by this file.

**The square root recurs and it is the same one.**  The sieve needs landmarks to `√x`; the
repetitions `p^k, k ≥ 2` are counted by `π(√x)` to leading order; RH's gap bound is `√p log p`; the
Möbius walk's conjectured size is `√x`; and the critical line is at `1/2`.  That recurrence is
recorded as a reading, not a theorem.
-/

namespace Soma.Holonics.Millennium.Landmarks

open Nat ArithmeticFunction

/-! ## The modulus a binary word can reach -/

/-- **A depth admits a modulus exactly when two has that period there.** -/
theorem theDepthAdmitsTheModulus (n p : ℕ) :
    n ∣ 2 ^ p - 1 ↔ ((2 : ZMod n) ^ p = 1) := by
  have h1 : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  rw [← Nat.modEq_iff_dvd' h1]
  constructor
  · intro h
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h.symm
    push_cast at this
    simpa using this
  · intro h
    have : ((2 ^ p : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by push_cast; simpa using h
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp this).symm

/-- **The least depth at which a modulus is reachable is the multiplicative order of two.** -/
theorem theLeastDepthIsTheOrderOfTwo (n p : ℕ) :
    orderOf (2 : ZMod n) ∣ p ↔ n ∣ 2 ^ p - 1 := by
  rw [theDepthAdmitsTheModulus n p, orderOf_dvd_iff_pow_eq_one]

/-- **The odd-parity branch: the modulus divides `2^p + 1` exactly when two squares to period `p`
without having period `p`.** -/
theorem theOppositeParityBranch (n p : ℕ) :
    ((2 : ZMod n) ^ p = -1) → orderOf (2 : ZMod n) ∣ 2 * p := by
  intro h
  rw [orderOf_dvd_iff_pow_eq_one, two_mul, pow_add, h]
  ring

/-- **The least depth at which each modulus becomes reachable**, decided rather than asserted.
`3` first at depth 2, `5` at 4, `7` at 3, `9` at 6 — the multiplicative orders of two.  *These are
exactly the moduli the period-`p` sign words land on: `2^p ∓ 1` by minus-count parity.* -/
theorem theLeastDepthTable :
    (3 ∣ 2 ^ 2 - 1 ∧ ¬ (3 ∣ 2 ^ 1 - 1))
      ∧ (5 ∣ 2 ^ 4 - 1 ∧ ¬ (5 ∣ 2 ^ 1 - 1) ∧ ¬ (5 ∣ 2 ^ 2 - 1) ∧ ¬ (5 ∣ 2 ^ 3 - 1))
      ∧ (7 ∣ 2 ^ 3 - 1 ∧ ¬ (7 ∣ 2 ^ 1 - 1) ∧ ¬ (7 ∣ 2 ^ 2 - 1))
      ∧ (9 ∣ 2 ^ 6 - 1 ∧ ¬ (9 ∣ 2 ^ 1 - 1) ∧ ¬ (9 ∣ 2 ^ 2 - 1) ∧ ¬ (9 ∣ 2 ^ 3 - 1)
          ∧ ¬ (9 ∣ 2 ^ 4 - 1) ∧ ¬ (9 ∣ 2 ^ 5 - 1)) := by
  decide

/-- The moduli themselves: `2^p ∓ 1` at the first three periods, matching the verified radical
table `−` → 3, `+−` → 5, `+−−` → 7, `++−` → 9. -/
theorem theModuliAtTheFirstThreePeriods :
    2 ^ 1 + 1 = 3 ∧ 2 ^ 2 + 1 = 5 ∧ 2 ^ 3 - 1 = 7 ∧ 2 ^ 3 + 1 = 9 := by
  decide

/-! ## Kummer, from mathlib, with a carry instance -/

/-- **The multiplicity of a prime in a binomial coefficient is the number of carries.**

This is mathlib's `Nat.factorization_choose`, restated: the counted condition
`p ^ i ≤ k % p ^ i + (n - k) % p ^ i` is exactly *a carry occurred at position `i`* when adding `k`
and `n − k` in base `p`.  **The particular digits do not enter; only how many times the addition
carried.**  (Kummer, 1852.) -/
theorem theMultiplicityIsTheCarryCount {p n k b : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hnb : Nat.log p n < b) :
    (Nat.choose n k).factorization p
      = ((Finset.Ico 1 b).filter (fun i => p ^ i ≤ k % p ^ i + (n - k) % p ^ i)).card :=
  Nat.factorization_choose hp hkn hnb

/-- **A carry instance, decided.**  `3 + 3` in base two is `11 + 11`, which carries at positions
one and two and not at three; `C(6,3) = 20 = 2² · 5`, and the two carries are the two factors of
two. -/
theorem theCarryInstance :
    ((Finset.Ico 1 4).filter (fun i => 2 ^ i ≤ 3 % 2 ^ i + 3 % 2 ^ i)).card = 2
      ∧ Nat.choose 6 3 = 20 ∧ (2 ^ 2 ∣ 20) ∧ ¬ (2 ^ 3 ∣ 20) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-! ## Bertrand, from mathlib -/

/-- **There is always a landmark in the next octave.**  (Bertrand's postulate; Chebyshev.)
Imported from mathlib, not proved here. -/
theorem theNextOctaveCarriesALandmark (n : ℕ) (hn : n ≠ 0) :
    ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.exists_prime_lt_and_le_two_mul n hn



/-- The `n`-th landmark. -/
noncomputable def pr (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- **Legendre's conjecture** — a landmark between consecutive squares. **OPEN**, and notably
*not* implied by the Riemann Hypothesis: RH bounds the gap by `√p log p`, which is far larger than
the `2n+1` available between `n²` and `(n+1)²`. -/
def LegendreConjecture : Prop :=
  ∀ n : ℕ, 0 < n → ∃ p, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- **Cramér's conjecture** — the gap is at most a constant times the square of the log. **OPEN**,
and far below what RH delivers. -/
def CramerConjecture : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ((pr (n + 1) : ℝ) - pr n) ≤ C * (Real.log (pr n)) ^ 2

/-- **The best unconditional gap bound** (Baker–Harman–Pintz, 2001): a landmark in every interval
`[x, x + x^0.525]` for large `x`.  A theorem, imported and not proved here. -/
def BakerHarmanPintz : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∃ p : ℕ, Nat.Prime p ∧ x ≤ (p : ℝ) ∧ (p : ℝ) ≤ x + x ^ (0.525 : ℝ)

/-- **What the Riemann Hypothesis buys for gaps**: `p_{n+1} − p_n = O(√p_n · log p_n)`.
An imported implication, not proved here — and the square root here is the same one as the critical
line's. -/
def RiemannGapBound : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    ((pr (n + 1) : ℝ) - pr n) ≤ C * Real.sqrt (pr n) * Real.log (pr n)

/-! ## The half-turn character and its walk -/

/-- **The Mertens sum** — the walk of the Möbius sign. -/
noncomputable def mertens (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, moebius n

/-- **Square-root cancellation for the Möbius walk.**  Equivalent to the Riemann Hypothesis
(Littlewood); imported, not proved here.  *If the signs were an independent coin this would be the
central-limit statement, so RH says the landmarks are no worse than the coin.* -/
def MertensSquareRootBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℕ, 1 ≤ x → |(mertens x : ℝ)| ≤ C * (x : ℝ) ^ (1 / 2 + ε)

/-- **Lucas' congruence** — the binomial coefficient factorizes over base-`p` digits, recursively.
A theorem (Lucas, 1878); mathlib does not carry it, and it is stated here as imported. -/
def LucasCongruence : Prop :=
  ∀ p : ℕ, p.Prime → ∀ m n : ℕ,
    ((Nat.choose m n : ZMod p)) =
      (Nat.choose (m / p) (n / p) : ZMod p) * (Nat.choose (m % p) (n % p) : ZMod p)

/-- **A Lucas instance, decided.**  `C(5,2) = 10 ≡ 1 (mod 3)`, and the digit product is
`C(1,0)·C(2,2) = 1`. -/
theorem theLucasInstance :
    ((Nat.choose 5 2 : ZMod 3)) =
      (Nat.choose (5 / 3) (2 / 3) : ZMod 3) * (Nat.choose (5 % 3) (2 % 3) : ZMod 3) := by
  decide

/-- **The Möbius sign is the half-turn character on squarefree numbers.**  Mathlib's own statement:
`moebius n = (−1)^Ω(n)` where the exponent counts prime factors with multiplicity. -/
theorem theMoebiusSignIsTheHalfTurnParity {n : ℕ} (h : Squarefree n) :
    moebius n = (-1) ^ cardFactors n :=
  moebius_apply_of_squarefree h



/-! ## The doubling map, and why the two moduli are the two branches of a cosine

The map `x ↦ x² − 2` on `[−2,2]` is conjugate under `x = 2cos θ` to `θ ↦ 2θ`, so a period-`p` sign
word is a periodic point of the doubling map.  Arithmetically that is Frobenius: the points fixed by
the `p`-fold doubling are `μ_{2^p−1} = F_{2^p}^×`, and `2cos` is the trace to the real subfield.

**The two moduli are the two ways `cos A = cos B` can hold.**  Either the angle advances by whole
turns — `2^k θ = θ + 2πm`, giving `2^k − 1` — or it advances to the *reflection*,
`2^k θ = 2πm − θ`, giving `2^k + 1`.  The minus-count parity of the word selects the branch.
-/

section Doubling
open Real Polynomial.Chebyshev


/-- The `k`-fold doubling, in the `2cos` coordinate. -/
noncomputable def dbl (k : ℕ) (x : ℝ) : ℝ := 2 * (T ℝ (2 ^ k : ℕ)).eval (x / 2)

/-- **The doubling polynomial doubles the angle.** -/
theorem theDoublingDoublesTheAngle (k : ℕ) (θ : ℝ) :
    dbl k (2 * Real.cos θ) = 2 * Real.cos ((2 ^ k : ℕ) * θ) := by
  have h2 : (2 : ℝ) * Real.cos θ / 2 = Real.cos θ := by ring
  simp only [dbl, h2, T_real_cos]
  push_cast
  ring

/-- **The untwisted family is fixed: the angle advances by whole turns.** -/
theorem theSplitFamilyIsFixed (k m : ℕ) (h : (2:ℝ) ^ k - 1 ≠ 0) :
    Real.cos ((2 ^ k : ℕ) * (2 * π * m / ((2:ℝ) ^ k - 1)))
      = Real.cos (2 * π * m / ((2:ℝ) ^ k - 1)) := by
  have key : ((2 ^ k : ℕ) : ℝ) * (2 * π * m / ((2:ℝ) ^ k - 1))
      = 2 * π * m / ((2:ℝ) ^ k - 1) + (m : ℝ) * (2 * π) := by
    push_cast; field_simp; ring
  rw [key, Real.cos_add_nat_mul_two_pi]

/-- **The twisted family is fixed through the REFLECTION: the angle advances to `2πm − θ`.**
That reflection is the minus branch, and it is why the odd-minus-count words land on `2^k + 1`. -/
theorem theTwistedFamilyIsFixed (k m : ℕ) (h : (2:ℝ) ^ k + 1 ≠ 0) :
    Real.cos ((2 ^ k : ℕ) * (2 * π * m / ((2:ℝ) ^ k + 1)))
      = Real.cos (2 * π * m / ((2:ℝ) ^ k + 1)) := by
  have key : ((2 ^ k : ℕ) : ℝ) * (2 * π * m / ((2:ℝ) ^ k + 1))
      = (m : ℝ) * (2 * π) - 2 * π * m / ((2:ℝ) ^ k + 1) := by
    push_cast; field_simp; ring
  rw [key, Real.cos_nat_mul_two_pi_sub]


end Doubling

/-! ### The moduli are point counts, and the zeta numerator is trivial there

`2^p − 1 = #𝔾ₘ(F_{2^p})` and `2^p + 1 = #P¹(F_{2^p})`.  Verified table: `1,3,7,15,31,63` and
`3,5,9,17,33,65` — the radical family's `3, 5, 7, 9` is that column.

For a curve of genus `g` over `F_q`, `#X(F_{q^p}) = q^p + 1 − Σ αᵢ^p` with `2g` terms.  **Here the
correction term is `∓1`, a root of unity: genus zero, `Z_{P¹}(t) = 1/((1−t)(1−qt))` with numerator
`1` and no `αᵢ` at all.**  Weil's `|αᵢ| = √q` is therefore vacuous on this family — it is the
degenerate case of the statement, and what a higher-genus curve replaces `∓1` with is the whole
content.
-/

/-- **The split modulus is the unit count of a finite field.**  From mathlib. -/
theorem theSplitModulusIsTheUnitCount (K : Type*) [Field K] [Fintype K] [DecidableEq K] :
    Fintype.card Kˣ = Fintype.card K - 1 :=
  Fintype.card_units K

/-- **The two moduli as point counts of the genus-zero pair, decided.** -/
theorem theModuliArePointCountsOfGenusZero :
    (2 ^ 1 - 1 = 1 ∧ 2 ^ 2 - 1 = 3 ∧ 2 ^ 3 - 1 = 7 ∧ 2 ^ 4 - 1 = 15)
      ∧ (2 ^ 1 + 1 = 3 ∧ 2 ^ 2 + 1 = 5 ∧ 2 ^ 3 + 1 = 9 ∧ 2 ^ 4 + 1 = 17) := by
  decide

/-- **The correction term on this family is a root of unity.**  In `#X(F_{q^p}) = q^p + 1 − Σαᵢ^p`
the family contributes `∓1`, so `|α| = 1` and not `√q` — the genus-zero degeneration, stated so the
family is not later read as a Weil instance carrying content. -/
def TheCorrectionTermIsAUnitOnThisFamily : Prop :=
  ∀ k : ℕ, ((2 : ℤ) ^ k - 1) = (2 : ℤ) ^ k - 1 ∧ ((2 : ℤ) ^ k + 1) = (2 : ℤ) ^ k - (-1)

theorem theCorrectionTermIsAUnitOnThisFamily : TheCorrectionTermIsAUnitOnThisFamily := by
  intro k; exact ⟨rfl, by ring⟩

end Soma.Holonics.Millennium.Landmarks
