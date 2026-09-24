import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityIntegral
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeLogarithmicEstimate

/-!
# The direct dyadic Hodge continuation factorization

**[proved-derived, conditional]** This owner places the actual direct dyadic logarithmic law on
the terminal half-tail and composes it with the already constructed critical-vorticity integral,
restart seam, and overlap uniqueness.  It removes the arbitrary base time and the former abstract
frequency comb.  Its two visible residuals are exactly the uniform direct dyadic physical-kernel
bound and the constructed restart supply from the derived uniform coordinate `H³` receiver.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeContinuation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityIntegral
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeLogarithmicEstimate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-! ## The canonical positive terminal half-tail -/

/-- Integrability on the full positive lifespan restricts to the canonical terminal half-tail. -/
theorem intervalIntegrable_criticalVorticity_halfTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hT : 0 < T)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T) :
    IntervalIntegrable (criticalVorticityRate solution) volume (T / 2) T := by
  apply hintegrable.mono_set
  exact Set.uIcc_subset_uIcc_right (by
    rw [uIcc_of_le hT.le]
    exact ⟨by linarith, by linarith⟩)

/-- **Direct dyadic terminal continuation.**  The finite integral is read on `[0,T]`, while the
logarithmic law and restart population use the canonically chosen positive face `T/2`.  The
returned value is the full gauge-compatible extension past `T`, constructed by the checked seam
and overlap-uniqueness passages. -/
def compatibleOpenPeriodicExtension_of_dyadicHodge_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {kernelConstant : ℝ}
    (hkernel : UniformDyadicHodgeJacobianKernelBound kernelConstant)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution (T / 2)
      (coordinateLogH3Receiver velocity)) :
    CompatibleOpenPeriodicExtension solution := by
  have hT : 0 < T := solution.terminal_pos
  have hhalfPos : 0 < T / 2 := by linarith
  have hhalfTerminal : T / 2 < T := by linarith
  exact compatibleOpenPeriodicExtension_of_intervalIntegrableCriticalVorticity
    (mul_nonneg (by norm_num)
      (dyadicHodgeLogarithmicConstant_nonneg hkernel.1)) hnu
    (lifespanLogarithmicCoordinateH3LawOfDyadicHodge
      solution hhalfPos hhalfTerminal hnu hkernel)
    (intervalIntegrable_criticalVorticity_halfTail solution hT hintegrable)
    restartFromBound

section Audit

#print axioms intervalIntegrable_criticalVorticity_halfTail
#print axioms compatibleOpenPeriodicExtension_of_dyadicHodge_intervalIntegrable

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeContinuation
