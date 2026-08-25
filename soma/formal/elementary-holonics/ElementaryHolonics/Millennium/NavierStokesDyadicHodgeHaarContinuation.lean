import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeContinuation
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeHaarReceiver

/-!
# Coordinate-Haar return through the direct dyadic continuation seam

This owner closes the composition from the eight coordinate-subset coefficient returns to the
already checked direct dyadic continuation passage.  The returned extension remains conditional
on the two mathematically genuine continuation hypotheses: integrability of the critical
vorticity rate and a restart supply from the terminal high-order receiver.

The coefficient-side residual is no longer an unnamed physical-kernel bound.  It is precisely an
inhabitant of `UniformLargeScaleDyadicHodgeSubsetMassReturn`, whose fields retain every coordinate
face and every Hodge entry.

Truth status: `[proved-derived, conditional] [formal-checked]`.
-/

noncomputable section

open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarContinuation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeContinuation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-- **Eight returned coordinate faces imply the direct dyadic continuation passage.**  This is
the exact composition theorem: the subset-mass return constructs the uniform physical `L¹`
kernel witness, and the existing continuation seam consumes that witness without introducing a
new analytic assumption. -/
def compatibleOpenPeriodicExtension_of_subsetMassReturn_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {massConstant : ℝ}
    (hmass : UniformLargeScaleDyadicHodgeSubsetMassReturn massConstant)
    (hintegrable :
      IntervalIntegrable (criticalVorticityRate solution) volume 0 T)
    (restartFromBound : RestartSupplyFromUniformHighOrderBound solution (T / 2)
      (coordinateLogH3Receiver velocity)) :
    CompatibleOpenPeriodicExtension solution :=
  compatibleOpenPeriodicExtension_of_dyadicHodge_intervalIntegrable
    solution hnu
    (uniformDyadicHodgeJacobianKernelBound_of_subsetMassReturn hmass)
    hintegrable restartFromBound

section Audit

#print axioms compatibleOpenPeriodicExtension_of_subsetMassReturn_intervalIntegrable

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarContinuation
