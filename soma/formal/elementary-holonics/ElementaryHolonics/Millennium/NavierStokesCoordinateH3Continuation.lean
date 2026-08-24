import ElementaryHolonics.Millennium.NavierStokesCoordinateH3FullEstimate
import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityIntegral

/-!
# Finite critical-vorticity continuation through the differentiated coordinate H³ receiver

This owner composes the receiver-corrected frequency comb with the constructed restart seam and
the exact terminal critical-vorticity integral.  Unlike the earlier operator-norm receiver route,
the derivative premise has disappeared: it is supplied by the genuine coordinate energy identity.

The complete forty-face production estimate is now constructed internally with coefficient
`10986`.  The two remaining analytic ports are exactly the actual low/middle/high Hodge comb and
the uniform local-restart theorem returned from a bound on this same coordinate receiver.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3Continuation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityIntegral
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FullEstimate
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

/-- The complete coordinate production estimate and the frequency comb return a continuation
receipt from the actual finite critical-vorticity integral.  Neither the high-order derivative nor
its forty-face production estimate is passed as an argument. -/
def coordinateH3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (hnu : 0 ≤ nu) (ha : 0 < a) (haT : a < T)
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a
      (coordinateLogH3Receiver velocity)) :
    LogarithmicHighOrderContinuationReceipt solution a
      (coordinateLogH3Receiver velocity)
      (Real.exp
        (Real.log (coordinateLogH3Receiver velocity a) *
          Real.exp ((10986 * combLogConstant) *
            (T - a + ∫ s in a..T, criticalVorticityRate solution s)))) := by
  let law := lifespanLogarithmicCoordinateH3LawOfFrequencyComb
    ha haT comb 10986 (by norm_num) (by
      intro t ht
      exact openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_envelope
        solution ⟨ha.trans_le ht.1, ht.2⟩ hnu
          (comb.jacobian_envelope t ht))
  exact scaledAugmentedCriticalVorticityContinuationFactorization_of_intervalIntegrable
    (mul_nonneg (by norm_num) combLogConstant_nonneg) hnu law
      hintegrable restartFromBound

/-- Projection of the preceding receipt to a genuine compatible solution beyond the terminal
time.  The result is manufactured by the checked splice and uniqueness passage; it is not present
in any analytic premise. -/
def compatibleOpenPeriodicExtension_of_coordinateH3FrequencyComb_intervalIntegrable
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}
    {jacobian low middle high : ℝ → ℝ}
    (hnu : 0 ≤ nu) (ha : 0 < a) (haT : a < T)
    (comb : OpenCoordinateH3FrequencyComb solution a jacobian low middle high)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume a T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution a
      (coordinateLogH3Receiver velocity)) :
    CompatibleOpenPeriodicExtension solution :=
  (coordinateH3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
    hnu ha haT comb hintegrable restartFromBound).extension

section Audit

#print axioms coordinateH3ContinuationReceiptOfFrequencyComb_of_intervalIntegrable
#print axioms compatibleOpenPeriodicExtension_of_coordinateH3FrequencyComb_intervalIntegrable

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateH3Continuation
