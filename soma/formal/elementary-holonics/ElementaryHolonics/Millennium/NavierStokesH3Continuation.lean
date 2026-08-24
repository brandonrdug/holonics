import ElementaryHolonics.Millennium.NavierStokesRestartSeam
import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityRate
import ElementaryHolonics.Millennium.NavierStokesVorticityStretchingComb

/-!
# Conditional H³ continuation through the constructed restart seam

This module only composes existing owners.  The restart seam and overlap uniqueness are discharged
for nonnegative viscosity, while the actual frequency comb, differentiated H³ production law,
accumulated critical-vorticity budget, and restart-from-bound attachment remain explicit inputs.
The return is a bounded conditional continuation receipt, not a BKM theorem or a global-regularity
claim.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesH3Continuation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesRestartSeam
open Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

/-- The scaled augmented critical-vorticity factorization with its seam premise discharged by the
piecewise restart construction.  The logarithmic law, accumulated budget, and local restart supply
remain visible. -/
def scaledAugmentedCriticalVorticityContinuationFactorization_withConstructedSeam
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {C : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (scaledAugmentedCriticalVorticityRate C solution))
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) * Real.exp (C * (T - a + M)))) :=
  scaledAugmentedCriticalVorticityContinuationFactorization_of_nonnegativeViscosity
    hC hnu law budget restartFromBound
      (openPeriodicRestartSpliceLaw_of_nonnegativeViscosity solution hnu)

/-- A concrete conditional H³ continuation receipt.  Its coefficient is the full product of the
order-three commutator constant and the frequency-comb base-conversion constant.  Every unresolved
analytic attachment remains an argument rather than being hidden in the conclusion. -/
def h3ContinuationReceiptOfFrequencyComb
    {T a M nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {jacobian low middle high H3Rate : ℝ → ℝ}
    {productionConstant : ℝ}
    (hnu : 0 ≤ nu) (ha : 0 < a) (haT : a < T)
    (comb : OpenH3FrequencyComb solution a jacobian low middle high)
    (hproductionConstant : 0 ≤ productionConstant)
    (hderiv : ∀ t ∈ Ico a T,
      HasDerivAt (periodicLogH3Receiver velocity) (H3Rate t) t)
    (hproduction : ∀ t ∈ Ico a T,
      H3Rate t ≤ productionConstant * jacobian t *
        periodicLogH3Receiver velocity t)
    (budget : OpenAccumulatedCriticalVorticityBudget (a := a) solution M)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a
      (periodicLogH3Receiver velocity)) :
    LogarithmicHighOrderContinuationReceipt solution a
      (periodicLogH3Receiver velocity)
      (Real.exp
        (Real.log (periodicLogH3Receiver velocity a) *
          Real.exp ((productionConstant * combLogConstant) * (T - a + M)))) := by
  let law := lifespanLogarithmicH3LawOfFrequencyComb ha haT comb
    productionConstant hproductionConstant hderiv hproduction
  exact scaledAugmentedCriticalVorticityContinuationFactorization_withConstructedSeam
    (h3CombAnalyticConstant_nonneg hproductionConstant) hnu law budget restartFromBound

section Audit

#print axioms scaledAugmentedCriticalVorticityContinuationFactorization_withConstructedSeam
#print axioms h3ContinuationReceiptOfFrequencyComb

end Audit

end Soma.Holonics.Millennium.NavierStokesH3Continuation
