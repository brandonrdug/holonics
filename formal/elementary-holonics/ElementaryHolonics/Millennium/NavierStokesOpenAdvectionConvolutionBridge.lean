import ElementaryHolonics.Millennium.NavierStokesH3Bilinear
import ElementaryHolonics.Millennium.NavierStokesOpenFourierSpatialSymbols
import ElementaryHolonics.Millennium.NavierStokesWeightedProductReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction

/-!
# Actual open advection is the complete infinite H³ convolution

**[proved-derived]** A smooth periodic velocity slice enters the existing complete `H³`
coefficient carrier.  Native product reconstruction identifies every scalar product coefficient,
and the genuine-torus derivative symbol identifies the differentiated factor.  Consequently the
Fourier coefficient of the actual field `Du(u)` is exactly the existing infinite advective
convolution, and its Leray receiver is exactly the existing projected carrier.

No terminal trace, finite Fourier aperture, or additional summability hypothesis is introduced.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedProductReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The old unweighted `H³` coefficient carrier of an actual smooth periodic slice. -/
def smoothSliceH3State
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u) :
    PeriodicVectorSobolevThree :=
  fun component ↦ smoothSliceSobolevCoefficients u hu hperiodic component

/-- The scalar native reconstruction of an actual component is its literal complex torus lift. -/
theorem reconstructedTorusComplexScalar_smoothSliceSobolevCoefficients
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (component : Fin 3) :
    reconstructedTorusComplexScalar
        (smoothSliceSobolevCoefficients u hu hperiodic component) =
      smoothSliceComponentLift u hu hperiodic component := by
  ext q
  calc
    reconstructedTorusComplexScalar
          (smoothSliceSobolevCoefficients u hu hperiodic component) q =
        reconstructedTorusComplexComponent
          (smoothSliceVectorWeightedH3 u hu hperiodic) component q := by
      rw [reconstructedTorusComplexScalar_apply,
        reconstructedTorusComplexComponent_apply]
      apply tsum_congr
      intro k
      congr 1
      change
        (smoothSliceSobolevCoefficients u hu hperiodic component).1 k =
          (weightedSobolevCoefficients 3
            (smoothSliceVectorWeightedH3 u hu hperiodic component)).1 k
      rw [unweighted_smoothSliceVectorWeightedH3_apply,
        smoothSliceSobolevCoefficients, smoothSliceFourierL2_apply]
    _ = smoothSliceComponentLift u hu hperiodic component q :=
      congrArg (fun field : C(SpatialTorus, ℂ) ↦ field q)
        (reconstructedTorusComplexComponent_smoothSliceVectorWeightedH3
          u hu hperiodic component)

/-- The genuine-torus Fourier coefficient of two actual smooth components is the complete
native `H³` convolution coefficient. -/
theorem torusSpatialFourierCoeff_smoothSliceComponentLift_mul
    (left right : InitialVelocity)
    (hleft : ContDiff ℝ ∞ left) (hright : ContDiff ℝ ∞ right)
    (hleftPeriodic : IsOnePeriodic left) (hrightPeriodic : IsOnePeriodic right)
    (leftComponent rightComponent : Fin 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff
        (smoothSliceComponentLift left hleft hleftPeriodic leftComponent *
          smoothSliceComponentLift right hright hrightPeriodic rightComponent) k =
      (scalarH3Product
        (smoothSliceSobolevCoefficients left hleft hleftPeriodic leftComponent)
        (smoothSliceSobolevCoefficients right hright hrightPeriodic rightComponent)).1 k := by
  have hproduct :
      reconstructedTorusComplexScalar
          (scalarH3Product
            (smoothSliceSobolevCoefficients left hleft hleftPeriodic leftComponent)
            (smoothSliceSobolevCoefficients right hright hrightPeriodic rightComponent)) =
        smoothSliceComponentLift left hleft hleftPeriodic leftComponent *
          smoothSliceComponentLift right hright hrightPeriodic rightComponent := by
    ext q
    rw [reconstructedTorusComplexScalar_scalarH3Product,
      reconstructedTorusComplexScalar_smoothSliceSobolevCoefficients,
      reconstructedTorusComplexScalar_smoothSliceSobolevCoefficients]
    rfl
  calc
    torusSpatialFourierCoeff
        (smoothSliceComponentLift left hleft hleftPeriodic leftComponent *
          smoothSliceComponentLift right hright hrightPeriodic rightComponent) k =
        torusSpatialFourierCoeff
          (reconstructedTorusComplexScalar
            (scalarH3Product
              (smoothSliceSobolevCoefficients left hleft hleftPeriodic leftComponent)
              (smoothSliceSobolevCoefficients right hright hrightPeriodic rightComponent))) k := by
      apply congrArg (fun field : SpatialTorus → ℂ ↦
        torusSpatialFourierCoeff field k)
      funext q
      exact congrArg (fun field : C(SpatialTorus, ℂ) ↦ field q) hproduct.symm
    _ = _ := by
      unfold reconstructedTorusComplexScalar
      rw [torusSpatialFourierCoeff_reconstructedTorusComplexComponent,
        nativeUnweightedComponent_scalarAsVectorWeighted]

/-- A selected derivative of a smooth slice is smooth to every finite order. -/
theorem directionalDerivativeField_contDiff_infty
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u) (coordinate : Fin 3) :
    ContDiff ℝ ∞ (directionalDerivativeField u coordinate) := by
  exact (hu.fderiv_right (by simp)).clm_apply contDiff_const

/-- The actual advective component descended to the genuine torus through the componentwise
product decomposition `u_j ∂_j u_i`. -/
def smoothAdvectionTorusComponent
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (output : Fin 3) : C(SpatialTorus, ℂ) :=
  ∑ coordinate : Fin 3,
    smoothSliceComponentLift u hu hperiodic coordinate *
      smoothSliceComponentLift (directionalDerivativeField u coordinate)
        (directionalDerivativeField_contDiff_infty hu coordinate)
        (directionalDerivativeField_isOnePeriodic hperiodic coordinate) output

/-- Every coefficient of the actual componentwise advection lift is the corresponding component
of the existing complete infinite `H³` advective convolution. -/
theorem torusSpatialFourierCoeff_smoothAdvectionTorusComponent
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (output : Fin 3) (k : SpatialFrequency) :
    torusSpatialFourierCoeff (smoothAdvectionTorusComponent u hu hperiodic output) k =
      h3AdvectiveConvolution (smoothSliceH3State u hu hperiodic)
        (smoothSliceH3State u hu hperiodic) output k := by
  rw [smoothAdvectionTorusComponent, torusSpatialFourierCoeff_finset_sum]
  rw [h3AdvectiveConvolution_apply
    (periodicVectorSobolevThree_hasAbsolutelySummableComponents
      (smoothSliceH3State u hu hperiodic))]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  change torusSpatialFourierCoeff
      (fun q ↦ smoothSliceComponentLift u hu hperiodic coordinate q *
        smoothSliceComponentLift (directionalDerivativeField u coordinate)
          (directionalDerivativeField_contDiff_infty hu coordinate)
          (directionalDerivativeField_isOnePeriodic hperiodic coordinate) output q) k = _
  have hproductCoefficient :=
    torusSpatialFourierCoeff_smoothSliceComponentLift_mul
      u (directionalDerivativeField u coordinate) hu
      (directionalDerivativeField_contDiff_infty hu coordinate)
      hperiodic (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
      coordinate output k
  change torusSpatialFourierCoeff
      (fun q ↦ smoothSliceComponentLift u hu hperiodic coordinate q *
        smoothSliceComponentLift (directionalDerivativeField u coordinate)
          (directionalDerivativeField_contDiff_infty hu coordinate)
          (directionalDerivativeField_isOnePeriodic hperiodic coordinate) output q) k = _
    at hproductCoefficient
  rw [hproductCoefficient, scalarH3Product_apply]
  apply tsum_congr
  intro p
  congr 1
  rw [smoothSliceH3State, smoothSliceSobolevCoefficients,
    smoothSliceFourierL2_apply]
  rw [smoothSliceSobolevCoefficients, smoothSliceFourierL2_apply]
  rw [vectorSpatialFourierCoeff_directionalDerivativeField
    u (hu.of_le (show (2 : WithTop ℕ∞) ≤ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) by
      exact WithTop.coe_le_coe.mpr le_top))
    hperiodic (k - p) output coordinate]
  rw [actualJacobianFourierMode_eq_multiplier]

/-- The actual Euclidean advective field `Du(u)`. -/
def actualAdvectionField (u : InitialVelocity) : InitialVelocity :=
  fun x ↦ fderiv ℝ u x (u x)

theorem actualAdvectionField_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (actualAdvectionField u) := by
  exact (hu.fderiv_right (by simp)).clm_apply hu

theorem actualAdvectionField_isOnePeriodic
    {u : InitialVelocity} (hperiodic : IsOnePeriodic u) :
    IsOnePeriodic (actualAdvectionField u) := by
  intro x coordinate
  change fderiv ℝ u (x + EuclideanSpace.single coordinate 1)
      (u (x + EuclideanSpace.single coordinate 1)) = fderiv ℝ u x (u x)
  rw [fderiv_isOnePeriodic u hperiodic x coordinate, hperiodic x coordinate]

/-- The componentwise torus field above is literally the quotient lift of `Du(u)`. -/
theorem smoothAdvectionTorusComponent_eq_actualAdvectionLift
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (output : Fin 3) :
    smoothAdvectionTorusComponent u hu hperiodic output =
      periodicTorusLift (complexVelocityComponent (actualAdvectionField u) output)
        (continuous_complexVelocityComponent
          (actualAdvectionField_contDiff hu).continuous output)
        (isOnePeriodic_complexVelocityComponent
          (actualAdvectionField_isOnePeriodic hperiodic) output) := by
  ext q
  let x : Space := euclideanRepresentative q
  have hprojection : euclideanToSpatialTorus x = q :=
    euclideanToSpatialTorus_representative q
  rw [← hprojection]
  simp only [smoothAdvectionTorusComponent, smoothSliceComponentLift,
    ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, periodicTorusLift_projection]
  change
    (∑ coordinate : Fin 3,
      (u x coordinate : ℂ) *
        (fderiv ℝ u x (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) output : ℂ)) =
      (fderiv ℝ u x (u x) output : ℂ)
  exact_mod_cast (by
    simpa [actualAdvectionField, advectionComponentLine, jacobianComponentLine,
      velocityComponentLine, affineSpatialLine, spatialBasisVector, mul_comm] using
      (advectionComponentLine_eq u x 0 output 0))

/-- The genuine Fourier coefficient of the literal smooth field `Du(u)` is the complete infinite
`H³` convolution coefficient. -/
theorem vectorSpatialFourierCoeff_actualAdvectionField_eq_h3AdvectiveConvolution
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) :
    vectorSpatialFourierCoeff (actualAdvectionField u)
        (actualAdvectionField_contDiff hu).continuous
        (actualAdvectionField_isOnePeriodic hperiodic) k =
      vectorCoefficientAt
        (h3AdvectiveConvolution (smoothSliceH3State u hu hperiodic)
          (smoothSliceH3State u hu hperiodic)) k := by
  funext output
  rw [vectorSpatialFourierCoeff_apply]
  rw [← smoothAdvectionTorusComponent_eq_actualAdvectionLift]
  exact torusSpatialFourierCoeff_smoothAdvectionTorusComponent
    u hu hperiodic output k

/-- Actual strict-interior open-solution advection coefficient. -/
def openActualAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  let u : InitialVelocity := fun x ↦ velocity x t.1
  vectorSpatialFourierCoeff (actualAdvectionField u)
    (actualAdvectionField_contDiff
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).continuous
    (actualAdvectionField_isOnePeriodic
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) k

/-- The actual open-solution coefficient is exactly the complete infinite `H³` convolution. -/
theorem openActualAdvectionMode_eq_h3AdvectiveConvolution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openActualAdvectionMode solution t k =
      vectorCoefficientAt
        (h3AdvectiveConvolution
          (smoothSliceH3State (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))
          (smoothSliceH3State (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))) k := by
  exact vectorSpatialFourierCoeff_actualAdvectionField_eq_h3AdvectiveConvolution
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- Applying Leray to the actual coefficient reaches the existing projected infinite carrier. -/
theorem lerayProjectMode_openActualAdvectionMode_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    lerayProjectMode k (openActualAdvectionMode solution t k) =
      lerayProjectedH3AdvectiveCoefficient
        (smoothSliceH3State (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))
        (smoothSliceH3State (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) k := by
  rw [openActualAdvectionMode_eq_h3AdvectiveConvolution]
  rfl

section Audit

#print axioms reconstructedTorusComplexScalar_smoothSliceSobolevCoefficients
#print axioms torusSpatialFourierCoeff_smoothSliceComponentLift_mul
#print axioms torusSpatialFourierCoeff_smoothAdvectionTorusComponent
#print axioms vectorSpatialFourierCoeff_actualAdvectionField_eq_h3AdvectiveConvolution
#print axioms openActualAdvectionMode_eq_h3AdvectiveConvolution
#print axioms lerayProjectMode_openActualAdvectionMode_eq

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
