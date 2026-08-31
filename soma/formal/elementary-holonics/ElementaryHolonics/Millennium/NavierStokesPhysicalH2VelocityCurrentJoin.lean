import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing

/-!
# The complete physical H2 current in the velocity multiplier chart

**[proved-derived; formal-checked]**  The literal derivative-weighted vorticity production
current is exactly the complete homogeneous `H3` velocity work.  At each frequency, curl--curl
Hodge transport supplies the leading Stokes factor and the inhomogeneous vorticity test supplies
the remaining `1 + lambda` factor.  Leray is invisible to the transverse Hermitian receiver, so
the sharp source may be read through the genuine complete velocity-advection coefficient.

This joins the previously separated stretching and transport descriptions before a norm: the
same physical current is one complete velocity-chart population carrying the multiplier
`lambda * (1 + lambda)`.  No finite-triad symmetrization, estimate, time integration, or
continuation claim is made in this file.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurlMultiplierSwing
open Soma.Holonics.Millennium.NavierStokesPhysicalH2CurrentTriadJoin
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-- The complete homogeneous velocity work on the actual open-solution slice.  Its source is the
genuine Fourier coefficient of the literal advective field, not a finite convolution fixture. -/
def completePhysicalH2VelocityCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∑' frequency : SpatialFrequency,
    homogeneousCoordinateH2ModeWork frequency
      (openPeriodicVelocityFourierMode solution t frequency)
      (openActualAdvectionMode solution t frequency)

/-- One mode of the vorticity current and one mode of the homogeneous velocity current are the
same physical occurrence in two exact Hodge charts. -/
theorem physicalH2VorticityModeCurrent_eq_velocityModeWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) •
          openPeriodicVorticityFourierMode solution t frequency)
        (vorticityNonlinearMode solution t frequency) =
      homogeneousCoordinateH2ModeWork frequency
        (openPeriodicVelocityFourierMode solution t frequency)
        (openActualAdvectionMode solution t frequency) := by
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier,
    vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient]
  calc
    sourceTestProductionReading
        ((((1 + torusStokesEigenvalue frequency : ℝ) : ℂ)) •
          frequencyCurlMultiplier frequency
            (openPeriodicVelocityFourierMode solution t frequency))
        (-frequencyCurlMultiplier frequency
          (unweightedSharpNonlinearSourceCoefficient
            (openVelocityWeightedH3State solution t) frequency)) =
      projectedCoordinateH1ModeWork frequency
          (openPeriodicVelocityFourierMode solution t frequency)
          (unweightedSharpNonlinearSourceCoefficient
            (openVelocityWeightedH3State solution t) frequency) +
        projectedCoordinateH2ModeWork frequency
          (openPeriodicVelocityFourierMode solution t frequency)
          (unweightedSharpNonlinearSourceCoefficient
            (openVelocityWeightedH3State solution t) frequency) :=
      derivativeWeighted_negCurlReading_eq_orderOne_add_orderTwo frequency
        (openPeriodicVelocityFourierMode solution t frequency)
        (unweightedSharpNonlinearSourceCoefficient
          (openVelocityWeightedH3State solution t) frequency)
        (openPeriodicVelocityMode_divergenceFree solution t frequency)
        (openSharpSourceMode_divergenceFree solution t frequency)
    _ = homogeneousCoordinateH2ModeWork frequency
        (openPeriodicVelocityFourierMode solution t frequency)
        (unweightedSharpNonlinearSourceCoefficient
          (openVelocityWeightedH3State solution t) frequency) :=
      (homogeneousCoordinateH2ModeWork_eq_orderOne_add_orderTwo _ _ _).symm
    _ = homogeneousCoordinateH2ModeWork frequency
        (openPeriodicVelocityFourierMode solution t frequency)
        (openActualAdvectionMode solution t frequency) := by
      unfold homogeneousCoordinateH2ModeWork
      rw [sourceTestProductionReading_openSharpSource_eq_actualAdvection]

/-- **Complete physical chart join.**  Stretching and transport are already composed inside the
literal vorticity source; the complete current can therefore be carried as one homogeneous
velocity population before any dyadic receiver. -/
theorem completePhysicalH2Current_eq_velocityCurrent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completePhysicalH2Current solution t =
      completePhysicalH2VelocityCurrent solution t := by
  unfold completePhysicalH2Current completePhysicalH2VelocityCurrent
  apply tsum_congr
  intro frequency
  exact physicalH2VorticityModeCurrent_eq_velocityModeWork solution t frequency

/-- The same complete velocity current explicitly carries the completed physical multiplier.
This form is the receiver to which finite closed-triad exchange symmetrization will attach. -/
theorem completePhysicalH2VelocityCurrent_eq_completedMultiplier
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    completePhysicalH2VelocityCurrent solution t =
      ∑' frequency : SpatialFrequency,
        -(physicalH2CurlEnergyMultiplier frequency).re *
          sourceTestProductionReading
            (openPeriodicVelocityFourierMode solution t frequency)
            (openActualAdvectionMode solution t frequency) := by
  unfold completePhysicalH2VelocityCurrent
  apply tsum_congr
  intro frequency
  exact homogeneousCoordinateH2ModeWork_eq_completedPhysicalMultiplier
    frequency
    (openPeriodicVelocityFourierMode solution t frequency)
    (openActualAdvectionMode solution t frequency)

section Audit

#print axioms physicalH2VorticityModeCurrent_eq_velocityModeWork
#print axioms completePhysicalH2Current_eq_velocityCurrent
#print axioms completePhysicalH2VelocityCurrent_eq_completedMultiplier

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2VelocityCurrentJoin
