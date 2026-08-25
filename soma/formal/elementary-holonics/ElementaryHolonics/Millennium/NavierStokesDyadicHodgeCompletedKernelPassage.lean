import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeHaarContinuation
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartSupply

/-!
# The completed dyadic Hodge kernel passage

**[proved-derived]** The source-specific eight-face coefficient construction now discharges the
kernel premise of the direct dyadic Beale--Kato--Majda logarithmic law.  This owner transports that
returned carrier through the existing continuation passage and exposes only the two genuine
terminal hypotheses: critical-vorticity integrability and restart supply.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeContinuation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarContinuation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeLogarithmicEstimate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply

/-- The exact physical-kernel constant returned by the completed low- and large-scale passages. -/
def dyadicHodgeCompletedKernelConstant : ℝ :=
  804357 + 216 * dyadicHodgeUniformSubsetMassConstant

/-- **[proved-derived]** The existential uniform physical-kernel interface is inhabited. -/
theorem hasUniformDyadicHodgeJacobianKernelBound_inhabited :
    HasUniformDyadicHodgeJacobianKernelBound := by
  exact ⟨dyadicHodgeCompletedKernelConstant,
    uniformDyadicHodgeJacobianKernelBound_inhabited⟩

/-- **[proved-derived]** The actual periodic logarithmic Jacobian estimate now has no coefficient
or kernel hypothesis. -/
theorem coordinateJacobianReceiver_le_completedDyadicHodge_logarithmic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateJacobianReceiver solution t ≤
      dyadicHodgeLogarithmicConstant dyadicHodgeCompletedKernelConstant *
        augmentedCriticalVorticityRate solution t *
          Real.log (coordinateLogH3Receiver velocity t) :=
  coordinateJacobianReceiver_le_dyadicHodge_logarithmic solution ht
    uniformDyadicHodgeJacobianKernelBound_inhabited

/-- **[proved-derived]** The lifespan logarithmic high-order law is constructed directly from the
solution and viscosity sign; the former uniform-kernel premise has been removed. -/
def lifespanLogarithmicCoordinateH3LawOfCompletedDyadicHodge
    {T a nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (haT : a < T) (hnu : 0 ≤ nu) :
    LifespanLogarithmicHighOrderLaw T a
      (coordinateLogH3Receiver velocity) (coordinateH3TimeWork velocity)
      (scaledAugmentedCriticalVorticityRate
        (10986 * dyadicHodgeLogarithmicConstant dyadicHodgeCompletedKernelConstant)
        solution) :=
  lifespanLogarithmicCoordinateH3LawOfDyadicHodge solution ha haT hnu
    uniformDyadicHodgeJacobianKernelBound_inhabited

/-- **[proved-derived, conditional]** The completed coefficient and kernel passage removes those
premises from continuation.  The two remaining arguments are displayed without packaging: finite
critical-vorticity accumulation and a terminal restart carrier. -/
def compatibleOpenPeriodicExtension_of_completedDyadicHodge
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution (T / 2)
      (coordinateLogH3Receiver velocity)) :
    CompatibleOpenPeriodicExtension solution :=
  compatibleOpenPeriodicExtension_of_dyadicHodge_intervalIntegrable
    solution hnu uniformDyadicHodgeJacobianKernelBound_inhabited
    hintegrable restartFromBound

/-- **[proved-derived, conditional]** For positive viscosity the already constructed weighted
classical restart owner removes the terminal restart premise.  Critical-vorticity integrability is
the sole remaining analytic argument of this continuation constructor. -/
noncomputable def compatibleOpenPeriodicExtension_of_integrableCriticalVorticity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T) :
    CompatibleOpenPeriodicExtension solution := by
  have hT : 0 < T := solution.terminal_pos
  have hhalfPos : 0 < T / 2 := by linarith
  have hhalfTerminal : T / 2 < T := by linarith
  exact compatibleOpenPeriodicExtension_of_completedDyadicHodge
    solution hnu.le hintegrable
      (restartSupplyFromUniformCoordinateBound
        solution hnu hhalfPos hhalfTerminal)

section Audit

#print axioms hasUniformDyadicHodgeJacobianKernelBound_inhabited
#print axioms coordinateJacobianReceiver_le_completedDyadicHodge_logarithmic
#print axioms lifespanLogarithmicCoordinateH3LawOfCompletedDyadicHodge
#print axioms compatibleOpenPeriodicExtension_of_completedDyadicHodge
#print axioms compatibleOpenPeriodicExtension_of_integrableCriticalVorticity

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
