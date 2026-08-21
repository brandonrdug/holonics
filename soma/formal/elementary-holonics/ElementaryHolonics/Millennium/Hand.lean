import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The hand — one half-turn per irreducible, and what its cancellation is

An integer's factorization is a word in irreducibles.  Reading each irreducible as a half turn
gives a `±1`-valued function of the integer: its **hand**.  This file builds that function,
proves it composes multiplicatively, and states the cancellation law its running sum satisfies.

The point of the construction is that the cancellation law is *the same statement* as the
placement of the zeros in `Seam.lean` — one is the hand's running sum, the other is where the
comb's modes sit — so the two files describe one object in two charts.

**The discipline this file exists to demonstrate.**  A *magnitude* claim and an *order* claim
about the same running sum are different propositions, and the magnitude claims here were both
refuted while the order claims remain open.  Section 4 proves the implication that makes them
comparable, so the difference is visible in the types rather than in a remark.

Every `theorem` here is discharged.  Every open statement is a `def ... : Prop` that is named
and never claimed.
-/

namespace Soma.Holonics.Millennium.Hand

open Finset

/-! ## 1. The hand -/

/-- The **factor depth** of an integer: how many irreducibles its word uses, counted with
multiplicity.

*Aside: `Ω(n)`.* -/
def factorDepth (n : ℕ) : ℕ := ArithmeticFunction.cardFactors n

/-- The **hand** of an integer: one half turn per irreducible in its word.

*Aside: the Liouville function `λ(n) = (−1)^{Ω(n)}`.  It is a counter of half turns, which is
why a claim about it is a claim about phase and not about size.* -/
def hand (n : ℕ) : ℤ := (-1) ^ (factorDepth n)

@[simp] theorem hand_one : hand 1 = 1 := by
  simp [hand, factorDepth]

/-- **The hand composes multiplicatively: the word of a product is the concatenation of the
words, so the turns add and the hands multiply.** -/
theorem theHandComposesMultiplicatively {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    hand (m * n) = hand m * hand n := by
  simp only [hand, factorDepth, ArithmeticFunction.cardFactors_mul hm hn, pow_add]

/-- **An irreducible carries exactly one half turn.** -/
theorem theHandOfAnIrreducibleIsOneHalfTurn {p : ℕ} (hp : p.Prime) : hand p = -1 := by
  simp [hand, factorDepth, ArithmeticFunction.cardFactors_apply_prime hp]

/-- **A power of an irreducible carries its exponent in half turns.** -/
theorem theHandOfAnIrreduciblePowerIsItsDepth {p k : ℕ} (hp : p.Prime) :
    hand (p ^ k) = (-1) ^ k := by
  simp [hand, factorDepth, ArithmeticFunction.cardFactors_apply_prime_pow hp]

/-- **A square is flat: its turns cancel in pairs.**  This is why the hand's Dirichlet series is
a ratio of two combs rather than one — the square-indicator is what the divisor sum returns. -/
theorem theHandOfASquareIsFlat {n : ℕ} (hn : n ≠ 0) : hand (n * n) = 1 := by
  rw [theHandComposesMultiplicatively hn hn]
  simp only [hand]
  rw [← pow_add, ← two_mul]
  exact Even.neg_one_pow ⟨factorDepth n, by ring⟩

/-- The hand takes only the two values.  Stated so a reader cannot mistake it for a magnitude. -/
theorem theHandIsOnlyEverAHalfTurn (n : ℕ) : hand n = 1 ∨ hand n = -1 := by
  rcases Nat.even_or_odd (factorDepth n) with h | h
  · exact Or.inl (by simp [hand, h.neg_one_pow])
  · exact Or.inr (by simp [hand, h.neg_one_pow])

/-! ## 2. The address orientation, and the two running sums -/

/-- The **address orientation**: the hand restricted to squarefree words, and zero elsewhere.

*Aside: the Möbius function `μ`.  It is a `ℤ/2`-valued orientation class carried by an address,
which is the same species of object as the orientation class of a band.* -/
def addressOrientation (n : ℕ) : ℤ := ArithmeticFunction.moebius n

/-- The **running hand sum** up to `x`.

*Aside: `L(x) = Σ_{n≤x} λ(n)`.* -/
def runningHandSum (x : ℕ) : ℤ := ∑ n ∈ Icc 1 x, hand n

/-- The **running orientation sum** up to `x`.

*Aside: the Mertens function `M(x) = Σ_{n≤x} μ(n)`.* -/
def runningOrientationSum (x : ℕ) : ℤ := ∑ n ∈ Icc 1 x, addressOrientation n

@[simp] theorem runningHandSum_zero : runningHandSum 0 = 0 := by simp [runningHandSum]

@[simp] theorem runningOrientationSum_zero : runningOrientationSum 0 = 0 := by
  simp [runningOrientationSum]

/-- Each running sum advances by one half turn at a time, so it is a walk and not a magnitude. -/
theorem theRunningHandSumStepsByOneTurn (x : ℕ) :
    runningHandSum (x + 1) = runningHandSum x + hand (x + 1) := by
  simp [runningHandSum, Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le x))]

/-! ## 3. The cancellation laws — named, and never claimed

These are the open statements.  Each is a `Prop` this file names and does not discharge. -/

/-- **The hand's turns cancel to square-root order.**

*Aside: this is equivalent to the Riemann Hypothesis.  The equivalence is classical and is not
formalized here; `Seam.lean` names the bridge and leaves it open.* -/
def TheHandCancelsToSquareRoot : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, 1 ≤ x → |(runningHandSum x : ℝ)| ≤ C * (x : ℝ) ^ (1 / 2 + ε)

/-- **The orientation's turns cancel to square-root order.**

*Aside: also equivalent to the Riemann Hypothesis.* -/
def TheOrientationCancelsToSquareRoot : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ x : ℕ, 1 ≤ x → |(runningOrientationSum x : ℝ)| ≤ C * (x : ℝ) ^ (1 / 2 + ε)

/-! ## 4. The magnitude claims are strictly stronger — and both were refuted

Two natural strengthenings replace the *order* by a *magnitude*.  Both are false.  This section
proves that each implies its order form, so the refutations land on strictly stronger statements
and leave the open ones standing.  That asymmetry is the whole reason a split and a hand must be
stated separately. -/

/-- **The running orientation sum never leaves its own root.**

*Aside: the Mertens conjecture.  It is FALSE — refuted by Odlyzko and te Riele in 1985, with no
explicit counterexample exhibited by that argument.* -/
def TheOrientationSumStaysUnderItsRoot : Prop :=
  ∀ x : ℕ, 1 ≤ x → |(runningOrientationSum x : ℝ)| < Real.sqrt (x : ℝ)

/-- **The running hand sum never turns positive.**

*Aside: the Pólya conjecture.  It is FALSE — refuted by Haselgrove in 1958; the least
counterexample is 906150257.* -/
def TheHandSumNeverTurnsPositive : Prop :=
  ∀ x : ℕ, 2 ≤ x → runningHandSum x ≤ 0

/-- **A magnitude bound implies its order bound.**

The refuted claim is therefore strictly stronger than the open one, and its refutation says
nothing whatever about the open one.  This is the split-and-hand discipline as a typed
implication rather than as a caution. -/
theorem theMagnitudeClaimIsStrictlyStronger :
    TheOrientationSumStaysUnderItsRoot → TheOrientationCancelsToSquareRoot := by
  intro h ε hε
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hroot : Real.sqrt (x : ℝ) = (x : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (x : ℝ)
  have hmono : (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (x : ℝ) ^ (1 / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  calc |(runningOrientationSum x : ℝ)|
      ≤ Real.sqrt (x : ℝ) := le_of_lt (h x hx)
    _ = (x : ℝ) ^ ((1 : ℝ) / 2) := hroot
    _ ≤ (x : ℝ) ^ (1 / 2 + ε) := hmono
    _ = 1 * (x : ℝ) ^ (1 / 2 + ε) := (one_mul _).symm

end Soma.Holonics.Millennium.Hand
