import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
import ElementaryHolonics.Millennium.NavierStokesOpenFourierMildIdentity

/-!
# Integration of the named open advection mode with the complete H³ carrier

**[proved-derived]** The named strict-interior advection coefficient and the independently
reconstructed actual coefficient are the same genuine-torus receiver.  The named nonlinear
vorticity source therefore factors exactly through the complete infinite `H³` advective
convolution.  Its curl also factors through the existing Leray-projected coefficient because the
discarded longitudinal mode has zero cross interaction with its own frequency.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The two independently constructed genuine-torus coefficients of the actual open-solution
advective field coincide exactly. -/
theorem openAdvectionMode_eq_openActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openAdvectionMode solution t k = openActualAdvectionMode solution t k := by
  unfold openAdvectionMode openActualAdvectionMode advectionField actualAdvectionField
  rfl

/-- The actual native `H³` coefficient state of one strict-interior velocity slice. -/
def openVelocityH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : PeriodicVectorSobolevThree :=
  smoothSliceH3State (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)

/-- The named nonlinear vorticity source is exactly the frequency curl of the complete infinite
`H³` advective convolution coefficient. -/
theorem vorticityNonlinearMode_eq_h3AdvectiveConvolution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k =
      -frequencyCurlMultiplier k
        (vectorCoefficientAt
          (h3AdvectiveConvolution (openVelocityH3State solution t)
            (openVelocityH3State solution t)) k) := by
  rw [vorticityNonlinearMode,
    openAdvectionMode_eq_openActualAdvectionMode,
    openActualAdvectionMode_eq_h3AdvectiveConvolution]
  unfold openVelocityH3State
  rfl

/-- A modewise Leray projection does not change its frequency curl: the removed component is
parallel to the frequency itself. -/
theorem frequencyCurlMultiplier_lerayProjectMode
    (k : SpatialFrequency) (mode : ComplexVector) :
    frequencyCurlMultiplier k (lerayProjectMode k mode) =
      frequencyCurlMultiplier k mode := by
  by_cases hk : k = 0
  · subst k
    simp
  · ext component
    fin_cases component <;>
      simp [frequencyCurlMultiplier, lerayProjectMode, hk, complexCross,
        complexFrequencyVector, crossProduct] <;>
      ring

/-- Equivalently, the named nonlinear vorticity source factors through the already-founded
Leray-projected complete `H³` advective coefficient. -/
theorem vorticityNonlinearMode_eq_lerayProjectedH3AdvectiveCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k =
      -frequencyCurlMultiplier k
        (lerayProjectedH3AdvectiveCoefficient
          (openVelocityH3State solution t) (openVelocityH3State solution t) k) := by
  rw [vorticityNonlinearMode_eq_h3AdvectiveConvolution,
    lerayProjectedH3AdvectiveCoefficient,
    frequencyCurlMultiplier_lerayProjectMode]

section Audit

#print axioms openAdvectionMode_eq_openActualAdvectionMode
#print axioms vorticityNonlinearMode_eq_h3AdvectiveConvolution
#print axioms frequencyCurlMultiplier_lerayProjectMode
#print axioms vorticityNonlinearMode_eq_lerayProjectedH3AdvectiveCoefficient

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
