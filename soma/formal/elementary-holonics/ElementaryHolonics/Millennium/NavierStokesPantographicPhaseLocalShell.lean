import ElementaryHolonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
import ElementaryHolonics.Millennium.NavierStokesTransportedPantographicSwingBand

/-!
# The transported pantographic swing at the actual phase-local shell receiver

**[proved-derived; formal-checked]**  The exact finite-band mild identity is specialized to each
actual dyadic vorticity shell.  The finite swing chain, its reconstruction residual, and the
frozen boundary action remain one signed spatial population under a single norm.  Consequently
their phase interaction is retained; the estimate separates only the earlier heat face from the
complete transported nonlinear population.

This is the PDE-owned entry to the remaining terminal spacetime shell-packing estimate.  It does
not assert that the shell population is terminal-time integrable.
-/

noncomputable section

open Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesPantographicPhaseLocalShell

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingBand

/-- The three returned nonlinear incidences remain combined after transport to one spatial
receiver.  A later norm therefore retains cancellation among chain, residual, and boundary. -/
def compactPantographicIntegratedPopulationBand
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  compactPantographicPartialChainIntegratedBand
      solution hs hst ht depth modes +
    compactPantographicResidualIntegratedBand
      solution hs hst ht depth modes +
    compactPantographicFrozenBoundaryBand solution hs hst ht modes

/-- The actual vorticity band is the earlier heat face minus the complete signed transported
pantographic population. -/
theorem openPeriodicVorticityBandProjector_eq_initialHeat_sub_combinedPantographicPopulation
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (modes : Finset SpatialFrequency) :
    openPeriodicVorticityBandProjector solution
        ⟨t, hs.trans_le hst, ht⟩ modes =
      compactInitialVorticityHeatBand solution hs hst ht modes -
        compactPantographicIntegratedPopulationBand
          solution hs hst ht depth modes := by
  simpa only [compactPantographicIntegratedPopulationBand] using
    openPeriodicVorticityBandProjector_eq_initialHeat_sub_pantographicPopulation
      solution hnu hs hst ht depth modes

/-- **Actual phase-local pantographic shell estimate.**  The norm is taken only after all three
nonlinear populations have reached the same signed torus shell.  No coefficientwise absolute
mass and no separation of the three interacting nonlinear faces occurs. -/
theorem openPeriodicVorticityDyadicShellSpatialSup_le_initialHeat_add_combinedPantographicPopulation
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth level : ℕ) :
    openPeriodicVorticityDyadicShellSpatialSup solution
        ⟨t, hs.trans_le hst, ht⟩ level ≤
      ‖compactInitialVorticityHeatBand solution hs hst ht
          (dyadicFrequencyShell level)‖ +
        ‖compactPantographicIntegratedPopulationBand
          solution hs hst ht depth (dyadicFrequencyShell level)‖ := by
  unfold openPeriodicVorticityDyadicShellSpatialSup
  rw [openPeriodicVorticityBandProjector_eq_initialHeat_sub_combinedPantographicPopulation
    solution hnu hs hst ht depth (dyadicFrequencyShell level)]
  exact norm_sub_le _ _

section Audit

#print axioms openPeriodicVorticityBandProjector_eq_initialHeat_sub_combinedPantographicPopulation
#print axioms openPeriodicVorticityDyadicShellSpatialSup_le_initialHeat_add_combinedPantographicPopulation

end Audit

end Soma.Holonics.Millennium.NavierStokesPantographicPhaseLocalShell
