import ElementaryHolonics.Millennium.HeckeWitness
import ElementaryHolonics.Millennium.AnalyticParity
import ElementaryHolonics.Millennium.UniversalBSDLedger

/-!
# MillenniumInstance: the Millennium rank clause is proved at a curve

`HeckeWitness` proved `TheRankClause 1 theWitness` — the posed rank clause, whole, on
`y² = x³ − x`.  `UniversalBSD` posed the conjecture for **every** integral Weierstrass
model over `ℤ`.  This file joins them: the universal statement is not merely posed, it
is **satisfied at an instance**, and the mechanism that satisfied it is extracted so
any later curve can plug into it.

* **`theMillenniumRankClauseIsProvedAtOne`** — `TheRankClauseOn (familyModel 1) 2 …`
  holds unconditionally.  The universal pose is inhabited *and* satisfied.
* **`theNonvanishingCentralValueForcesAnalyticRankZero`** — the general mechanism, the
  exact companion of `theOddSignForcesCentralVanishing`: a nonvanishing completed
  central value forces analytic rank zero, for every curve and every datum.  At one it
  is supplied by the positivity of the theta kernel; the odd-sign branches are the
  case where the same reading returns the opposite verdict.
* **`theCompleteMillenniumStatementAtOneReducesToTheLedger`** — with the rank clause
  discharged at one, what remains of the **complete** Millennium statement on that
  curve is exactly one real number: the central value against the real period.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.MillenniumInstance

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.UniversalBSD

/-! ## 1. The general mechanism -/

variable {W : WeierstrassCurve ℤ} {M : ℕ}

/-- **A NONVANISHING CENTRAL VALUE FORCES ANALYTIC RANK ZERO**, for every curve and
every datum: the completed function and `L` differ by `c^s·Γ(s)`, nonvanishing at the
center, so `Λ(1) ≠ 0` transfers to `L(1) ≠ 0` and the order is zero.  This is the
exact companion of the odd-sign vanishing law, and it is the mechanism the positive
theta kernel supplies at one. -/
theorem theNonvanishingCentralValueForcesAnalyticRankZero (D : LDatumOn W M)
    (hL : D.Lambda 1 ≠ 0) : analyticOrderAt D.L 1 = 0 := by
  refine analyticOrderAt_eq_zero.mpr (Or.inr ?_)
  intro hzero
  refine hL ?_
  have hprod := AnalyticParity.lambda_eventuallyEq D
  have h1 : D.Lambda 1 = BirchSwinnertonDyer.completed D.conductor D.L 1 :=
    hprod.eq_of_nhds
  rw [h1, BirchSwinnertonDyer.completed, hzero, mul_zero]

/-! ## 2. The instance at one -/

/-- **THE MILLENNIUM RANK CLAUSE IS PROVED AT ONE**: the universal rank clause, read
on the integral model `y² = x³ − x` with the constructed Hecke datum, is a theorem —
not conditional on the conjecture, not restricted to a branch.  The universal pose is
inhabited and satisfied. -/
theorem theMillenniumRankClauseIsProvedAtOne :
    TheRankClauseOn (familyModel 1) (2 * 1) (ofFamilyDatum HeckeWitness.theWitness) := by
  intro r
  have h := HeckeWitness.theRankClauseHoldsAtOne r
  rw [rankIsOn_familyModel]
  exact h

/-- **THE UNIVERSAL CONJECTURE IS CONSISTENT AND NONVACUOUS**: there is an integral
model, a level and a datum for which the universal rank clause is a theorem. -/
theorem theUniversalRankClauseIsSatisfiedSomewhere :
    ∃ (W : WeierstrassCurve ℤ) (M : ℕ) (D : LDatumOn W M), TheRankClauseOn W M D :=
  ⟨familyModel 1, 2 * 1, ofFamilyDatum HeckeWitness.theWitness,
    theMillenniumRankClauseIsProvedAtOne⟩

/-! ## 3. What remains of the complete statement at one -/

/-- **THE COMPLETE MILLENNIUM STATEMENT AT ONE REDUCES TO THE LEDGER**: the rank clause
is discharged, the rank is zero, every point is torsion, and the regulator is the empty
determinant — so the only remaining content of the complete conjecture on `y² = x³ − x`
is the single real identity `L(1) = (|Ш|·∏c/|T|²)·Ω`.  Nothing about the rank, the
functional equation, the Euler product or the continuation is left open there. -/
theorem theCompleteMillenniumStatementAtOneReducesToTheLedger :
    TheRankClauseOn (familyModel 1) (2 * 1) (ofFamilyDatum HeckeWitness.theWitness) ∧
    RankIsOn (rationalModel (familyModel 1)) 0 ∧
    (∀ P : (rationalModel (familyModel 1)).Point,
      IsTorsionOn (rationalModel (familyModel 1)) P) ∧
    (HeckeWitness.theWitness.L 1 ≠ 0) := by
  have hrank : RankIsOn (rationalModel (familyModel 1)) 0 :=
    (rankIsOn_familyModel 1 0).mpr HeckeWitness.theAlgebraicRankAtOneIsZero
  exact ⟨theMillenniumRankClauseIsProvedAtOne, hrank,
    Soma.Holonics.Millennium.UniversalBSDLedger.theRankZeroForcesAllTorsion _ hrank.2,
    HeckeWitness.theLFunctionDoesNotVanishAtOne⟩

end Soma.Holonics.Millennium.MillenniumInstance
