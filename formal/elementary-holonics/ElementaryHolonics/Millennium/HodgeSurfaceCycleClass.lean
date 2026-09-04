import ElementaryHolonics.Millennium.HodgeProductSingularCohomologyDual

/-!
# The ruling-divisor cycle class in the singular-cohomology dual

This file consumes the singular-cohomology dual immediately.  Rational combinations of the two
actual projection fibres are sent to functionals on genuine rational singular homology by the
fixed-factor/varying-factor ruling pairing.  The constructed cellular cycle class and this
singular receiver then commute through an exact linear equivalence.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSurfaceCycleClass

open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineDivisors
open Soma.Holonics.Millennium.HodgeProjectiveLineCellularCohomology
open Soma.Holonics.Millennium.HodgeProductSingularCohomologyDual

/-- [proved-derived; formal-checked] Constructed cellular degree-two cohomology rebases to the
singular-cohomology dual by the fixed-factor/varying-factor ruling receiver. -/
def cellularToSingularCohomologyEquivalence :
    CellularH2 ≃ₗ[ℚ] SurfaceDegreeTwoRationalSingularCohomology :=
  cellularH2BidegreeEquiv.trans singularCohomologyDual

/-- [definition] The cycle class of an actual rational ruling divisor is its evaluation
functional on genuine rational singular homology. -/
def singularDivisorCycleClass :
    RationalRulingDivisor →ₗ[ℚ] SurfaceDegreeTwoRationalSingularCohomology :=
  singularCohomologyDual.toLinearMap.comp divisorBidegreeEquiv.toLinearMap

/-- [proved-derived; formal-checked] The singular cycle class evaluates by the exact
fixed-factor/varying-factor pairing on every ruling-homology coordinate. -/
theorem singularDivisorCycleClass_evaluation
    (divisor : RationalRulingDivisor) (homology : Bidegree) :
    singularDivisorCycleClass divisor
        (surfaceRulingHomologyEquivalence homology) =
      rulingEvaluation (divisorBidegreeEquiv divisor) homology := by
  exact singularCohomologyDual_evaluation (divisorBidegreeEquiv divisor) homology

/-- [proved-derived; formal-checked] The cellular and singular ruling-divisor cycle-class maps
commute.  Both source and target are independently constructed carriers; the square is not a
dimension-count substitute. -/
theorem divisorCycleClassNaturality (divisor : RationalRulingDivisor) :
    cellularToSingularCohomologyEquivalence (cellularCycleClass divisor) =
      singularDivisorCycleClass divisor := by
  change singularCohomologyDual
      (cellularH2BidegreeEquiv (cellularCycleClass divisor)) =
    singularCohomologyDual (divisorBidegreeEquiv divisor)
  apply congrArg singularCohomologyDual
  change cellularH2BidegreeEquiv
      (cellularH2BidegreeEquiv.symm (divisorBidegreeEquiv divisor)) =
    divisorBidegreeEquiv divisor
  exact cellularH2BidegreeEquiv.apply_symm_apply _

theorem firstDivisorCycleClass_on_firstRuling :
    singularDivisorCycleClass (Pi.single Ruling.first 1)
        (surfaceRulingHomologyEquivalence firstFibre) = 1 := by
  rw [singularDivisorCycleClass_evaluation, divisorBidegreeEquiv_first]
  simp [rulingEvaluation, firstFibre]

theorem firstDivisorCycleClass_on_secondRuling :
    singularDivisorCycleClass (Pi.single Ruling.first 1)
        (surfaceRulingHomologyEquivalence secondFibre) = 0 := by
  rw [singularDivisorCycleClass_evaluation, divisorBidegreeEquiv_first]
  simp [rulingEvaluation, firstFibre, secondFibre]

theorem secondDivisorCycleClass_on_firstRuling :
    singularDivisorCycleClass (Pi.single Ruling.second 1)
        (surfaceRulingHomologyEquivalence firstFibre) = 0 := by
  rw [singularDivisorCycleClass_evaluation, divisorBidegreeEquiv_second]
  simp [rulingEvaluation, firstFibre, secondFibre]

theorem secondDivisorCycleClass_on_secondRuling :
    singularDivisorCycleClass (Pi.single Ruling.second 1)
        (surfaceRulingHomologyEquivalence secondFibre) = 1 := by
  rw [singularDivisorCycleClass_evaluation, divisorBidegreeEquiv_second]
  simp [rulingEvaluation, secondFibre]

section Audit

#print axioms cellularToSingularCohomologyEquivalence
#print axioms singularDivisorCycleClass
#print axioms singularDivisorCycleClass_evaluation
#print axioms divisorCycleClassNaturality

end Audit

end Soma.Holonics.Millennium.HodgeSurfaceCycleClass
