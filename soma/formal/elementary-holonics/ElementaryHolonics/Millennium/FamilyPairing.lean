import ElementaryHolonics.Millennium.FamilyGenocchi
import ElementaryHolonics.Millennium.FamilyWitness
import ElementaryHolonics.Millennium.FamilyFiveDescent
import ElementaryHolonics.Millennium.FamilySevenDescent

/-!
# FamilyPairing: what the posed conjecture forces on each branch

**The rank clause meets the branch theorems.**  Genocchi's law (algebraic rank
exactly zero at `p ≡ 3 (mod 8)`) and the family witness's central vanishing
(analytic rank positive at `p ≡ 5 (mod 8)`) pair with the posed rank clause:

* **`theConjectureForcesAnalyticRankZeroOnTheThreeModEightBranch`** — under the
  rank clause, **every** analytic datum at a prime `p ≡ 3 (mod 8)` has analytic
  rank zero: the algebraic side is a theorem, so the clause pins the analytic side.
* **`theConjectureForcesAPointOfInfiniteOrderOnTheFiveModEightBranch`** — under the
  rank clause for the standing family witness, every prime `p ≡ 5 (mod 8)` carries
  a rational point of infinite order on `y² = x³ − p²x`: the analytic side is a
  theorem, so the clause demands the point — every such prime is a congruent
  number, conditionally on the posed conjecture.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyPairing

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer

/-- **Under the rank clause, the analytic rank vanishes at every prime
`p ≡ 3 (mod 8)`**, for every analytic datum: Genocchi's law is the algebraic half,
and the clause transports it. -/
theorem theConjectureForcesAnalyticRankZeroOnTheThreeModEightBranch
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 3) (W : LDatum p)
    (hclause : TheRankClause p W) :
    analyticRank W = (0 : ℕ∞) :=
  (hclause 0).mpr (FamilyGenocchi.theGenocchiLawHoldsOnTheThreeModEightBranch hp8)

/-- **Under the rank clause for the family witness, every prime `p ≡ 5 (mod 8)`
carries a rational point of infinite order** on `y² = x³ − p²x`: the central value
vanishes as a theorem, so the clause refuses algebraic rank zero — conditionally on
the posed conjecture, every such prime is a congruent number. -/
theorem theConjectureForcesAPointOfInfiniteOrderOnTheFiveModEightBranch
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5)
    (hclause : TheRankClause p
      (FamilyWitness.theWitnessAtEverySplitPrime p (by omega))) :
    AlgebraicRankAtLeast p 1 := by
  by_contra hno
  have h0 : AlgebraicRankIs p 0 :=
    ⟨⟨fun i => i.elim0, fun c _ i => i.elim0⟩, by simpa using hno⟩
  have hzero := (hclause 0).mpr h0
  exact FamilyWitness.theAnalyticRankIsPositiveOnTheFiveModEightBranch p hp8
    (by simpa using hzero)


/-- **Under the rank clause for the odd-prime witness, every prime
`p ≡ 5, 7 (mod 8)` carries a rational point of infinite order** — conditionally on
the posed conjecture, every such prime is a congruent number.  With Genocchi's
unconditional rank zero at `p ≡ 3 (mod 8)`, the conjecture's dial across the odd
residues is now fully posed and half-discharged. -/
theorem theConjectureForcesAPointOfInfiniteOrderOnTheOddSignBranches
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5 ∨ p % 8 = 7)
    (hclause : TheRankClause p
      (FamilyWitness.theWitnessAtEveryOddPrime p
        (by rcases hp8 with h | h <;> omega))) :
    AlgebraicRankAtLeast p 1 := by
  by_contra hno
  have h0 : AlgebraicRankIs p 0 :=
    ⟨⟨fun i => i.elim0, fun c _ i => i.elim0⟩, by simpa using hno⟩
  have hzero := (hclause 0).mpr h0
  exact FamilyWitness.theAnalyticRankIsPositiveOnTheOddSignBranches p hp8
    (by simpa using hzero)


/-- **THE CONJECTURE IS SQUEEZED TO A SINGLE POINT ON THE FIVE-MOD-EIGHT BRANCH**:
under the rank clause for the family witness at a prime `p ≡ 5 (mod 8)`, the
algebraic rank is **exactly one** and the analytic rank is **exactly one** — the
central vanishing supplies the lower bound as a theorem, the eight-cell descent
supplies the upper bound as a theorem, and the clause carries both onto the
analytic side.  All that separates the branch from an unconditional proof of the
conjecture\'s rank clause here is the single point of infinite order itself. -/
theorem theConjectureIsSqueezedToASinglePointOnTheFiveModEightBranch
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5)
    (hclause : TheRankClause p
      (FamilyWitness.theWitnessAtEverySplitPrime p (by omega))) :
    AlgebraicRankIs p 1 ∧
      analyticRank (FamilyWitness.theWitnessAtEverySplitPrime p (by omega)) =
        (1 : ℕ∞) := by
  have h1 : AlgebraicRankAtLeast p 1 :=
    theConjectureForcesAPointOfInfiniteOrderOnTheFiveModEightBranch p hp8 hclause
  have h2 : ¬ AlgebraicRankAtLeast p 2 :=
    FamilyFiveDescent.theRankIsAtMostOneAtEveryFiveModEightPrime hp8
  have hIs : AlgebraicRankIs p 1 := ⟨h1, h2⟩
  exact ⟨hIs, (hclause 1).mpr hIs⟩



/-- **THE CONJECTURE IS SQUEEZED TO A SINGLE POINT ON THE ENTIRE ODD-SIGN LOCUS**:
under the rank clause for the odd-prime witness at any prime `p ≡ 5, 7 (mod 8)`,
the algebraic rank is **exactly one** and the analytic rank is **exactly one** —
the odd functional-equation sign supplies the lower bound as a theorem, the
eight-cell descents on both branches supply the upper bound as a theorem, and the
clause carries both onto the analytic side.  Everywhere the completed `L` is
forced to vanish at the center, one rational point of infinite order is all that
remains between this family and the conjecture\'s rank clause. -/
theorem theConjectureIsSqueezedToASinglePointOnTheOddSignLocus
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5 ∨ p % 8 = 7)
    (hclause : TheRankClause p
      (FamilyWitness.theWitnessAtEveryOddPrime p
        (by rcases hp8 with h | h <;> omega))) :
    AlgebraicRankIs p 1 ∧
      analyticRank (FamilyWitness.theWitnessAtEveryOddPrime p
        (by rcases hp8 with h | h <;> omega)) = (1 : ℕ∞) := by
  have h1 : AlgebraicRankAtLeast p 1 :=
    theConjectureForcesAPointOfInfiniteOrderOnTheOddSignBranches p hp8 hclause
  have h2 : ¬ AlgebraicRankAtLeast p 2 := by
    rcases hp8 with h | h
    · exact FamilyFiveDescent.theRankIsAtMostOneAtEveryFiveModEightPrime h
    · exact FamilySevenDescent.theRankIsAtMostOneAtEverySevenModEightPrime h
  have hIs : AlgebraicRankIs p 1 := ⟨h1, h2⟩
  exact ⟨hIs, (hclause 1).mpr hIs⟩

end Soma.Holonics.Millennium.FamilyPairing

