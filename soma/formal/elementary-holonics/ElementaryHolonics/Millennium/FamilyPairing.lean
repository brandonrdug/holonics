import ElementaryHolonics.Millennium.FamilyGenocchi
import ElementaryHolonics.Millennium.FamilyWitness

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

end Soma.Holonics.Millennium.FamilyPairing
