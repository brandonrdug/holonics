import ElementaryHolonics.Millennium.NavierStokesOfficialBridge
import ElementaryHolonics.Millennium.NavierStokesRestartSeam

/-!
# Pressure normalization on an open periodic lifespan

**[proved-derived; formal-checked]** Spatial pressure anchoring is an exact gauge rebase of an
open periodic Navier--Stokes solution.  It leaves the velocity, force, initial datum, and pressure
gradient unchanged while returning the origin-normalized pressure representative required by a
cofinal atlas.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesPressureNormalization

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOfficialBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesRestartSeam

/-- Anchoring at the spatial origin returns the declared pressure gauge at every nonnegative
time (and in fact at every real time). -/
theorem pressureNormalized_anchoredPressure (pressure : PressureField) :
    PressureNormalized (anchoredPressure pressure) := by
  intro t _
  simp [anchoredPressure]

/-- Rebase an open periodic solution into the origin-normalized pressure chart without changing
its velocity or any source data. -/
def OpenPeriodicSolutionOn.normalizePressure
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    OpenPeriodicSolutionOn T nu initial force velocity (anchoredPressure pressure) where
  terminal_pos := solution.terminal_pos
  momentum x t ht := by
    have hm := solution.momentum x t ht
    have hp := OpenPeriodicSolutionOn.pressureSpatialSmooth solution ht
    rw [gradient_anchoredPressure_eq pressure x t
      (hp.differentiable (by norm_num) x)]
    exact hm
  incompressible := solution.incompressible
  initial := solution.initial
  velocitySmooth := solution.velocitySmooth
  pressureSmooth :=
    Soma.Holonics.Millennium.NavierStokesRestartSeam.OpenPeriodicSolutionOn.anchoredPressureSmooth
      solution
  velocityPeriodic := solution.velocityPeriodic
  pressurePeriodic t ht :=
    anchoredPressure_isOnePeriodic (solution.pressurePeriodic t ht)

/-- The normalized solution carries the exact pressure-normalization receipt expected by the
official cofinal atlas. -/
theorem OpenPeriodicSolutionOn.normalizePressure_pressureNormalized
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    PressureNormalized (anchoredPressure pressure) :=
  pressureNormalized_anchoredPressure pressure

section Audit

#print axioms pressureNormalized_anchoredPressure
#print axioms OpenPeriodicSolutionOn.normalizePressure
#print axioms OpenPeriodicSolutionOn.normalizePressure_pressureNormalized

end Audit

end Soma.Holonics.Millennium.NavierStokesPressureNormalization
