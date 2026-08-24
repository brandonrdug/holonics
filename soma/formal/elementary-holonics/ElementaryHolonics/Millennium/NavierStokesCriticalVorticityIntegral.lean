import ElementaryHolonics.Millennium.NavierStokesH3Continuation

/-!
# From a finite critical-vorticity integral to the open-tail continuation budget

**[proved-derived]** The source owner is the genuine torus-vorticity receiver from
`NavierStokesCriticalVorticityRate`; the target port is its existing open-tail accumulated-rate
budget.  The event is restriction of one nonnegative integrable time population from `[a,T]` to
each `[a,t]`, and the returned consequence is the exact terminal integral as a common bound.

This removes a representational gap: `IntervalIntegrable` of the actual critical receiver up to
`T` now supplies the family of partial-integral inequalities consumed by logarithmic Grönwall.
It assumes no terminal value or terminal continuity of the receiver.  The logarithmic H³ law and
uniform local restart theorem remain open analytic inputs to the continuation projections below.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesCriticalVorticityIntegral

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesH3Continuation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

/-- **[proved-derived]** Integrability of the genuine nonnegative critical-vorticity receiver on
the complete addressed interval gives the exact terminal integral as a common upper budget for
all strict-tail partial integrals. -/
def openAccumulatedCriticalVorticityBudget_of_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T) :
    OpenAccumulatedCriticalVorticityBudget (a := a) solution
      (∫ s in a..T, criticalVorticityRate solution s) where
  accumulated_le := by
    intro t ht
    exact intervalIntegral.integral_mono_interval
      (f := criticalVorticityRate solution)
      (c := a) (d := T) le_rfl ht.1 ht.2.le
      (Filter.Eventually.of_forall
        (criticalVorticityRate_nonneg solution))
      hintegrable

/-- **[proved-derived]** The existing scaled logarithmic continuation factorization can therefore
consume an actual finite integral, rather than a separately postulated family of partial budgets.
The return still exposes the high-order law and uniform local-restart attachment. -/
def scaledAugmentedCriticalVorticityContinuationFactorization_of_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {C : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (scaledAugmentedCriticalVorticityRate C solution))
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H) :
    LogarithmicHighOrderContinuationReceipt solution a H
      (Real.exp (Real.log (H a) *
        Real.exp (C *
          (T - a + ∫ s in a..T, criticalVorticityRate solution s)))) :=
  scaledAugmentedCriticalVorticityContinuationFactorization_withConstructedSeam
    hC hnu law
      (openAccumulatedCriticalVorticityBudget_of_intervalIntegrable hintegrable)
      restartFromBound

/-- **[proved-derived]** Projection of the preceding exact factorization to the requested
gauge-compatible extension past `T`.  Its result is constructed by the checked restart seam and
overlap-uniqueness owners; it is not contained in the integrability premise. -/
def compatibleOpenPeriodicExtension_of_intervalIntegrableCriticalVorticity
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField} {H H' : ℝ → ℝ}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {C : ℝ} (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (law : LifespanLogarithmicHighOrderLaw T a H H'
      (scaledAugmentedCriticalVorticityRate C solution))
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a H) :
    CompatibleOpenPeriodicExtension solution :=
  (scaledAugmentedCriticalVorticityContinuationFactorization_of_intervalIntegrable
    hC hnu law hintegrable restartFromBound).extension

/-! ## The currently available concrete H³ projection -/

/-- **[proved-derived]** The checked frequency-comb/H³ factorization with its budget premise
replaced by the actual finite critical-vorticity integral.  The differentiated production law,
comb realization, and local restart theorem remain explicit and therefore auditable. -/
def h3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
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
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a
      (periodicLogH3Receiver velocity)) :
    LogarithmicHighOrderContinuationReceipt solution a
      (periodicLogH3Receiver velocity)
      (Real.exp
        (Real.log (periodicLogH3Receiver velocity a) *
          Real.exp ((productionConstant * combLogConstant) *
            (T - a + ∫ s in a..T, criticalVorticityRate solution s)))) :=
  h3ContinuationReceiptOfFrequencyComb hnu ha haT comb hproductionConstant
    hderiv hproduction
      (openAccumulatedCriticalVorticityBudget_of_intervalIntegrable hintegrable)
      restartFromBound

/-- **[proved-derived]** The resulting full gauge-compatible extension projection.  The finite
integral is on the actual torus-vorticity receiver; none of the remaining analytic inputs already
contains an extension receipt. -/
def compatibleOpenPeriodicExtension_of_h3FrequencyComb_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
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
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a
      (periodicLogH3Receiver velocity)) :
    CompatibleOpenPeriodicExtension solution :=
  (h3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
    hnu ha haT comb hproductionConstant hderiv hproduction hintegrable
      restartFromBound).extension

section Audit

#print axioms openAccumulatedCriticalVorticityBudget_of_intervalIntegrable
#print axioms scaledAugmentedCriticalVorticityContinuationFactorization_of_intervalIntegrable
#print axioms compatibleOpenPeriodicExtension_of_intervalIntegrableCriticalVorticity
#print axioms h3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
#print axioms compatibleOpenPeriodicExtension_of_h3FrequencyComb_intervalIntegrable

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalVorticityIntegral
