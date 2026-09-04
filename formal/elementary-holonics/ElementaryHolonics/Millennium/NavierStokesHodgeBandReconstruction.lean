import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors

/-!
# Exact Hodge reconstruction of every finite Jacobian band

The torus Fourier owner proves curl descent and nonzero-mode Hodge ascent for an actual
incompressible solution slice.  The finite-band owner separately synthesizes the actual Jacobian
coefficients.  This file composes those two passages: every Jacobian mode, including the zero
mode, is the Hodge reconstruction of the corresponding actual vorticity mode, and therefore every
declared finite Jacobian population is exactly a synthesis of reconstructed vorticity pins.

This is an algebraic/Fourier reconstruction receipt.  It proves no radius-independent physical
kernel bound, Calderon--Zygmund estimate, logarithmic inequality, or infinite Fourier-series
convergence.
-/

noncomputable section

open MeasureTheory

namespace Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The Jacobian coefficient reconstructed from one addressed vorticity coefficient.  At the
zero frequency the outer derivative multiplier makes the result zero, so the totalized Hodge
division introduces no spurious mean Jacobian. -/
def hodgeJacobianMode
    (frequency : SpatialFrequency) (vorticityMode : ComplexVector) :
    ComplexJacobianArray :=
  fourierJacobianMode frequency
    (nonzeroModeHodgeReconstruction frequency vorticityMode)

@[simp]
theorem hodgeJacobianMode_zero (vorticityMode : ComplexVector) :
    hodgeJacobianMode 0 vorticityMode = 0 := by
  funext component coordinate
  simp [hodgeJacobianMode, fourierJacobianMode]

/-- **Complete modewise Hodge ascent for the actual solution Jacobian.**  Nonzero modes use the
checked Hodge inversion; the zero mode is discharged by the exact derivative multiplier. -/
theorem hodgeJacobianMode_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    hodgeJacobianMode frequency
        (openPeriodicVorticityFourierMode solution t frequency) =
      openPeriodicJacobianFourierMode solution t frequency := by
  by_cases hfrequency : frequency = 0
  · subst frequency
    rw [hodgeJacobianMode_zero,
      openPeriodicJacobianFourierMode_eq_fourierJacobianMode]
    funext component coordinate
    simp [fourierJacobianMode]
  · rw [hodgeJacobianMode,
      openPeriodicSolutionOn_nonzeroModeHodgeReconstruction solution t hfrequency,
      openPeriodicJacobianFourierMode_eq_fourierJacobianMode]

/-- Finite synthesis of the actual vorticity coefficients after exact Hodge ascent. -/
def openPeriodicHodgeJacobianBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexJacobianArray) :=
  finiteFourierSynthesis
    (fun frequency ↦ hodgeJacobianMode frequency
      (openPeriodicVorticityFourierMode solution t frequency))
    modes

/-- **Exact finite-population reconstruction.**  The Hodge-ascent synthesis is the existing
actual Jacobian band, with every addressed mode and component retained. -/
theorem openPeriodicHodgeJacobianBandProjector_eq_actual
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (modes : Finset SpatialFrequency) :
    openPeriodicHodgeJacobianBandProjector solution t modes =
      openPeriodicJacobianBandProjector solution t modes := by
  unfold openPeriodicHodgeJacobianBandProjector
    openPeriodicJacobianBandProjector
  congr 1
  funext frequency
  exact hodgeJacobianMode_openPeriodicVorticityFourierMode
    solution t frequency

/-- The reconstructed finite band has exactly the admitted reconstructed coefficient and zero
outside the declared population. -/
theorem mFourierCoeff_openPeriodicHodgeJacobianBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (modes : Finset SpatialFrequency)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicHodgeJacobianBandProjector solution t modes) frequency =
      if frequency ∈ modes then
        hodgeJacobianMode frequency
          (openPeriodicVorticityFourierMode solution t frequency)
      else 0 := by
  exact mFourierCoeff_finiteFourierSynthesis _ _ _

section Audit

#print axioms hodgeJacobianMode_zero
#print axioms hodgeJacobianMode_openPeriodicVorticityFourierMode
#print axioms openPeriodicHodgeJacobianBandProjector_eq_actual
#print axioms mFourierCoeff_openPeriodicHodgeJacobianBandProjector

end Audit

end Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
