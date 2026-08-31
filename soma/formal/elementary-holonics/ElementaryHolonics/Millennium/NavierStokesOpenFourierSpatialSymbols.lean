import ElementaryHolonics.Millennium.NavierStokesOpenFourierModeEvolution
import ElementaryHolonics.Millennium.NavierStokesFiniteFourierHeat

/-!
# Genuine-torus spatial symbols for the open-solution mode ODE

This module assembles the spatial derivative multipliers needed by the strict-interior mode
evolution owner.  It remains entirely inside the admitted open lifespan.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesH3Production

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The selected spatial derivative of a vector field. -/
def directionalDerivativeField (u : InitialVelocity) (coordinate : Fin 3) :
    InitialVelocity :=
  fun x ↦ fderiv ℝ u x (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)

theorem directionalDerivativeField_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ 2 u) (coordinate : Fin 3) :
    ContDiff ℝ 1 (directionalDerivativeField u coordinate) := by
  exact (hu.fderiv_right (by norm_num)).clm_apply contDiff_const

theorem directionalDerivativeField_isOnePeriodic
    {u : InitialVelocity} (hu : IsOnePeriodic u) (coordinate : Fin 3) :
    IsOnePeriodic (directionalDerivativeField u coordinate) := by
  intro x i
  exact congrArg
    (fun D : Space →L[ℝ] Space ↦
      D (EuclideanSpace.basisFun (Fin 3) ℝ coordinate))
    (fderiv_isOnePeriodic u hu x i)

/-- Iterating the fixed-direction derivative agrees with the matching entry of the actual second
Fréchet derivative when the source is genuinely C². -/
theorem directionalDerivativeField_iterate_eq_secondFDeriv
    {u : InitialVelocity} (hu : ContDiff ℝ 2 u) (coordinate : Fin 3) (x : Space) :
    directionalDerivativeField (directionalDerivativeField u coordinate) coordinate x =
      fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)
        (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) := by
  let e : Space := EuclideanSpace.basisFun (Fin 3) ℝ coordinate
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have happly := fderiv_clm_apply hDu (differentiableAt_const e)
  change fderiv ℝ (fun y ↦ fderiv ℝ u y e) x e =
    fderiv ℝ (fderiv ℝ u) x e e
  rw [happly]
  simp

/-- The Euclidean vector Laplacian is the sum of the three iterated directional fields. -/
theorem laplacian_eq_sum_directionalDerivativeField_iterate
    {u : InitialVelocity} (hu : ContDiff ℝ 2 u) :
    Δ u = fun x ↦ ∑ coordinate : Fin 3,
      directionalDerivativeField
        (directionalDerivativeField u coordinate) coordinate x := by
  funext x
  rw [laplacian_eq_sum_secondFDeriv]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  exact (directionalDerivativeField_iterate_eq_secondFDeriv hu coordinate x).symm

/-- The Laplacian of a smooth periodic field retains all three unit periods. -/
theorem laplacian_isOnePeriodic
    {u : InitialVelocity} (hu : ContDiff ℝ 2 u) (hperiodic : IsOnePeriodic u) :
    IsOnePeriodic (Δ u) := by
  rw [laplacian_eq_sum_directionalDerivativeField_iterate hu]
  intro x i
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  exact directionalDerivativeField_isOnePeriodic
    (directionalDerivativeField_isOnePeriodic hperiodic coordinate) coordinate x i

/-- The first directional derivative coefficient is the matching actual Jacobian entry. -/
theorem vectorSpatialFourierCoeff_directionalDerivativeField
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) (component coordinate : Fin 3) :
    vectorSpatialFourierCoeff (directionalDerivativeField u coordinate)
        (directionalDerivativeField_contDiff hu coordinate).continuous
        (directionalDerivativeField_isOnePeriodic hperiodic coordinate) k component =
      actualJacobianFourierMode u (hu.of_le (by norm_num)) hperiodic
        k component coordinate := by
  rw [vectorSpatialFourierCoeff_apply]
  unfold actualJacobianFourierMode
  apply congrArg (fun field : C(SpatialTorus, ℂ) ↦
    torusSpatialFourierCoeff field k)
  ext q
  change
    ((fderiv ℝ u (euclideanRepresentative q)
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)) component : ℂ) =
      ((jacobianMatrix (fderiv ℝ u (euclideanRepresentative q))
        component coordinate : ℝ) : ℂ)
  simp [jacobianMatrix_apply]

/-- Two applications of the proved first-derivative multiplier give the exact diagonal
second-derivative symbol. -/
theorem diagonalSecondDerivativeFourierMode_eq_multiplier_sq
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) (component coordinate : Fin 3) :
    actualJacobianFourierMode (directionalDerivativeField u coordinate)
        (directionalDerivativeField_contDiff hu coordinate)
        (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
        k component coordinate =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) ^ 2 *
        vectorSpatialFourierCoeff u hu.continuous hperiodic k component := by
  rw [actualJacobianFourierMode_eq_multiplier
    (directionalDerivativeField u coordinate)
    (directionalDerivativeField_contDiff hu coordinate)
    (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
    k component coordinate]
  rw [vectorSpatialFourierCoeff_directionalDerivativeField
    u hu hperiodic k component coordinate]
  rw [actualJacobianFourierMode_eq_multiplier
    u (hu.of_le (by norm_num)) hperiodic k component coordinate]
  ring

/-- The scalar torus Fourier receiver commutes with every finite sum of continuous fields. -/
theorem torusSpatialFourierCoeff_finset_sum
    {ι : Type*} (s : Finset ι) (field : ι → C(SpatialTorus, ℂ))
    (k : SpatialFrequency) :
    torusSpatialFourierCoeff ((∑ i ∈ s, field i : C(SpatialTorus, ℂ))) k =
      ∑ i ∈ s, torusSpatialFourierCoeff (field i) k := by
  classical
  simp only [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff,
    ContinuousMap.sum_apply]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [] with q
    rw [Finset.smul_sum]
  · intro i hi
    exact continuousMap_integrable_on_compact
      (UnitAddTorus.mFourier (-k) * field i)

/-- The coefficient of the actual vector Laplacian is the sum of the three actual diagonal
second-derivative coefficients. -/
theorem vectorSpatialFourierCoeff_laplacian_eq_sum_diagonal
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) (component : Fin 3) :
    vectorSpatialFourierCoeff (Δ u) (laplacian_contDiff hu).continuous
        (laplacian_isOnePeriodic
          (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic) k component =
      ∑ coordinate : Fin 3,
        actualJacobianFourierMode (directionalDerivativeField u coordinate)
          (((hu.fderiv_right (by simp)).clm_apply contDiff_const).of_le
            (WithTop.coe_le_coe.mpr le_top))
          (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
          k component coordinate := by
  rw [vectorSpatialFourierCoeff_apply]
  let hdirInf (coordinate : Fin 3) :
      ContDiff ℝ ∞ (directionalDerivativeField u coordinate) :=
    (hu.fderiv_right (by simp)).clm_apply contDiff_const
  let hdir (coordinate : Fin 3) :
      ContDiff ℝ 2 (directionalDerivativeField u coordinate) :=
    (hdirInf coordinate).of_le (WithTop.coe_le_coe.mpr le_top)
  let field (coordinate : Fin 3) : C(SpatialTorus, ℂ) :=
    periodicTorusLift
      (complexVelocityComponent
        (directionalDerivativeField (directionalDerivativeField u coordinate) coordinate)
        component)
      (continuous_complexVelocityComponent
        (directionalDerivativeField_contDiff (hdir coordinate) coordinate).continuous
        component)
      (isOnePeriodic_complexVelocityComponent
        (directionalDerivativeField_isOnePeriodic
          (directionalDerivativeField_isOnePeriodic hperiodic coordinate) coordinate)
        component)
  have hlift :
      periodicTorusLift (complexVelocityComponent (Δ u) component)
          (continuous_complexVelocityComponent (laplacian_contDiff hu).continuous component)
          (isOnePeriodic_complexVelocityComponent
            (laplacian_isOnePeriodic
              (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic) component) =
        ∑ coordinate : Fin 3, field coordinate := by
    ext q
    change (((Δ u) (euclideanRepresentative q) component : ℝ) : ℂ) =
      ∑ coordinate : Fin 3,
        ((directionalDerivativeField
          (directionalDerivativeField u coordinate) coordinate
          (euclideanRepresentative q) component : ℝ) : ℂ)
    rw [laplacian_eq_sum_directionalDerivativeField_iterate
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))]
    simp
  rw [hlift, torusSpatialFourierCoeff_finset_sum Finset.univ field k]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [← vectorSpatialFourierCoeff_directionalDerivativeField
    (directionalDerivativeField u coordinate) (hdir coordinate)
    (directionalDerivativeField_isOnePeriodic hperiodic coordinate)
    k component coordinate]
  rw [vectorSpatialFourierCoeff_apply]

/-- **Exact genuine-torus Laplacian symbol.** -/
theorem vectorSpatialFourierCoeff_laplacian_eq_stokes
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (k : SpatialFrequency) :
    vectorSpatialFourierCoeff (Δ u) (laplacian_contDiff hu).continuous
        (laplacian_isOnePeriodic
          (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic) k =
      -(torusStokesEigenvalue k : ℂ) •
        vectorSpatialFourierCoeff u hu.continuous hperiodic k := by
  ext component
  rw [vectorSpatialFourierCoeff_laplacian_eq_sum_diagonal
    u hu hperiodic k component]
  simp_rw [diagonalSecondDerivativeFourierMode_eq_multiplier_sq
    u (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic k component]
  simp only [Pi.smul_apply]
  unfold torusStokesEigenvalue frequencySquared
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  rw [Finset.mul_sum]
  have hterm (coordinate : Fin 3) :
      (Real.pi : ℂ) ^ 2 * (-1 : ℂ) * (k coordinate : ℂ) ^ 2 *
          vectorSpatialFourierCoeff u hu.continuous hperiodic k component * 4 =
        -((Real.pi : ℂ) ^ 2 *
          vectorSpatialFourierCoeff u hu.continuous hperiodic k component *
          (k coordinate : ℂ) ^ 2 * 4) := by ring
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_mul]

/-! ## Scalar pressure and its gradient symbol -/

def complexScalarField (p : Space → ℝ) : Space → ℂ :=
  fun x ↦ (p x : ℂ)

def complexScalarDirectionalDerivative
    (p : Space → ℝ) (coordinate : Fin 3) : Space → ℂ :=
  fun x ↦ (fderiv ℝ p x (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) : ℂ)

theorem continuous_complexScalarField
    {p : Space → ℝ} (hp : Continuous p) :
    Continuous (complexScalarField p) :=
  Complex.continuous_ofReal.comp hp

theorem isOnePeriodic_complexScalarField
    {p : Space → ℝ} (hp : IsOnePeriodic p) :
    IsOnePeriodic (complexScalarField p) := by
  intro x i
  exact congrArg (fun r : ℝ ↦ (r : ℂ)) (hp x i)

theorem continuous_complexScalarDirectionalDerivative
    {p : Space → ℝ} (hp : ContDiff ℝ 1 p) (coordinate : Fin 3) :
    Continuous (complexScalarDirectionalDerivative p coordinate) := by
  exact Complex.continuous_ofReal.comp
    ((ContinuousLinearMap.apply ℝ ℝ
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate)).continuous.comp
        (hp.continuous_fderiv (by norm_num)))

theorem isOnePeriodic_complexScalarDirectionalDerivative
    {p : Space → ℝ} (hp : IsOnePeriodic p) (coordinate : Fin 3) :
    IsOnePeriodic (complexScalarDirectionalDerivative p coordinate) := by
  intro x i
  exact congrArg
    (fun D : Space →L[ℝ] ℝ ↦
      (D (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) : ℂ))
    (fderiv_isOnePeriodic p hp x i)

/-- The quotient lifts of a smooth periodic scalar and its selected derivative form the genuine
torus coordinate-derivative pair. -/
theorem periodicTorusLift_isCoordinateDerivative_scalar
    {p : Space → ℝ} (hp : ContDiff ℝ 1 p) (hperiodic : IsOnePeriodic p)
    (coordinate : Fin 3) :
    IsCoordinateDerivative coordinate
      (periodicTorusLift (complexScalarField p)
        (continuous_complexScalarField hp.continuous)
        (isOnePeriodic_complexScalarField hperiodic))
      (periodicTorusLift (complexScalarDirectionalDerivative p coordinate)
        (continuous_complexScalarDirectionalDerivative hp coordinate)
        (isOnePeriodic_complexScalarDirectionalDerivative hperiodic coordinate)) := by
  intro tail anchor
  let scalarLift := periodicTorusLift (complexScalarField p)
    (continuous_complexScalarField hp.continuous)
    (isOnePeriodic_complexScalarField hperiodic)
  let derivativeLift := periodicTorusLift
    (complexScalarDirectionalDerivative p coordinate)
    (continuous_complexScalarDirectionalDerivative hp coordinate)
    (isOnePeriodic_complexScalarDirectionalDerivative hperiodic coordinate)
  have hscalarLine :
      (fun s : ℝ ↦ firstCoordinateSlice
        (scalarLift.comp (coordinateReindexTorusMap coordinate)) tail
          (s : UnitAddCircle)) =
      fun s : ℝ ↦ complexScalarField p
        (coordinateLinePoint coordinate tail anchor s) := by
    funext s
    change scalarLift
        (coordinateReindexTorus coordinate
          (joinFirstTorus (s : UnitAddCircle) tail)) = _
    rw [← euclideanToSpatialTorus_coordinateLinePoint]
    exact periodicTorusLift_projection _ _ _ _
  have hderivativeAt :
      firstCoordinateSlice
        (derivativeLift.comp (coordinateReindexTorusMap coordinate)) tail
          (anchor : UnitAddCircle) =
      complexScalarDirectionalDerivative p coordinate
        (coordinateLinePoint coordinate tail anchor anchor) := by
    change derivativeLift
        (coordinateReindexTorus coordinate
          (joinFirstTorus (anchor : UnitAddCircle) tail)) = _
    rw [← euclideanToSpatialTorus_coordinateLinePoint]
    exact periodicTorusLift_projection _ _ _ _
  have hpAlongLine : HasDerivAt
      (fun s : ℝ ↦ complexScalarField p
        (coordinateLinePoint coordinate tail anchor s))
      (complexScalarDirectionalDerivative p coordinate
        (coordinateLinePoint coordinate tail anchor anchor)) anchor := by
    have hcomposed :=
      (hp.differentiable (by norm_num)
        (coordinateLinePoint coordinate tail anchor anchor)).hasFDerivAt.comp_hasDerivAt
          anchor (coordinateLinePoint_hasDerivAt coordinate tail anchor)
    have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt anchor hcomposed
    simpa [Function.comp_def, complexScalarField,
      complexScalarDirectionalDerivative] using hcomplex
  rw [hscalarLine, hderivativeAt]
  exact hpAlongLine

/-- Genuine-torus coefficient of a smooth periodic real scalar. -/
def scalarFourierMode
    (p : Space → ℝ) (hp : Continuous p) (hperiodic : IsOnePeriodic p)
    (k : SpatialFrequency) : ℂ :=
  torusSpatialFourierCoeff
    (periodicTorusLift (complexScalarField p)
      (continuous_complexScalarField hp)
      (isOnePeriodic_complexScalarField hperiodic)) k

/-- One scalar directional derivative has the exact genuine-torus frequency multiplier. -/
theorem scalarDirectionalDerivativeFourierMode_eq_multiplier
    (p : Space → ℝ) (hp : ContDiff ℝ 1 p) (hperiodic : IsOnePeriodic p)
    (k : SpatialFrequency) (coordinate : Fin 3) :
    torusSpatialFourierCoeff
        (periodicTorusLift (complexScalarDirectionalDerivative p coordinate)
          (continuous_complexScalarDirectionalDerivative hp coordinate)
          (isOnePeriodic_complexScalarDirectionalDerivative hperiodic coordinate)) k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
        scalarFourierMode p hp.continuous hperiodic k := by
  exact torusSpatialFourierCoeff_coordinateDerivative coordinate _ _
    (periodicTorusLift_isCoordinateDerivative_scalar hp hperiodic coordinate) k

/-- The selected gradient component is exactly the selected scalar directional derivative. -/
theorem gradient_component_eq_directionalDerivative
    (p : Space → ℝ) (hp : ContDiff ℝ 1 p) (x : Space) (coordinate : Fin 3) :
    gradient p x coordinate =
      fderiv ℝ p x (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) := by
  rw [← EuclideanSpace.inner_basisFun_real
    (Fin 3) (gradient p x : Space) coordinate]
  simpa using (inner_gradient_left (hp.differentiable (by norm_num) x) :
    inner ℝ (gradient p x)
      (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) =
        fderiv ℝ p x (EuclideanSpace.basisFun (Fin 3) ℝ coordinate))

/-- **Exact genuine-torus pressure-gradient symbol.** -/
theorem vectorSpatialFourierCoeff_gradient_eq_frequency
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (hperiodic : IsOnePeriodic p)
    (k : SpatialFrequency) :
    vectorSpatialFourierCoeff (gradient p) (gradient_contDiff hp).continuous
        (gradient_isOnePeriodic p hperiodic) k =
      fun coordinate ↦
        (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
          scalarFourierMode p hp.continuous hperiodic k := by
  ext coordinate
  rw [vectorSpatialFourierCoeff_apply]
  let gradientLift := periodicTorusLift
    (complexVelocityComponent (gradient p) coordinate)
    (continuous_complexVelocityComponent (gradient_contDiff hp).continuous coordinate)
    (isOnePeriodic_complexVelocityComponent
      (gradient_isOnePeriodic p hperiodic) coordinate)
  let derivativeLift := periodicTorusLift
    (complexScalarDirectionalDerivative p coordinate)
    (continuous_complexScalarDirectionalDerivative
      (hp.of_le (WithTop.coe_le_coe.mpr le_top)) coordinate)
    (isOnePeriodic_complexScalarDirectionalDerivative hperiodic coordinate)
  have hlift : gradientLift = derivativeLift := by
    ext q
    change ((gradient p (euclideanRepresentative q) coordinate : ℝ) : ℂ) =
      ((fderiv ℝ p (euclideanRepresentative q)
        (EuclideanSpace.basisFun (Fin 3) ℝ coordinate) : ℝ) : ℂ)
    rw [gradient_component_eq_directionalDerivative p
      (hp.of_le (WithTop.coe_le_coe.mpr le_top))]
  change torusSpatialFourierCoeff gradientLift k = _
  rw [hlift]
  exact scalarDirectionalDerivativeFourierMode_eq_multiplier p
    (hp.of_le (WithTop.coe_le_coe.mpr le_top)) hperiodic k coordinate

/-- Curl annihilates the exact pressure-gradient mode. -/
theorem frequencyCurlMultiplier_gradientFourierMode_eq_zero
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (hperiodic : IsOnePeriodic p)
    (k : SpatialFrequency) :
    frequencyCurlMultiplier k
      (vectorSpatialFourierCoeff (gradient p) (gradient_contDiff hp).continuous
        (gradient_isOnePeriodic p hperiodic) k) = 0 := by
  rw [vectorSpatialFourierCoeff_gradient_eq_frequency p hp hperiodic k]
  ext component
  fin_cases component <;>
    simp [frequencyCurlMultiplier, complexCross, complexFrequencyVector,
      crossProduct] <;> ring

/-! ## Strict-interior open-solution assembly -/

/-- The actual pressure-gradient coefficient of an admitted open solution slice. -/
def openPressureGradientMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  vectorSpatialFourierCoeff (gradient (fun x ↦ pressure x t.1))
    (gradient_contDiff
      (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2)).continuous
    (gradient_isOnePeriodic (fun x ↦ pressure x t.1)
      (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) k

/-- Pressure curl cancellation for the actual open-solution pressure slice. -/
theorem openPeriodicSolutionOn_frequencyCurl_pressureGradientMode_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    frequencyCurlMultiplier k (openPressureGradientMode solution t k) = 0 := by
  exact frequencyCurlMultiplier_gradientFourierMode_eq_zero
    (fun x ↦ pressure x t.1)
    (openPeriodicSolutionOn_pressureSlice_contDiff solution t.2)
    (solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- The actual Laplacian coefficient of an admitted open velocity slice. -/
def openVelocityLaplacianMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  vectorSpatialFourierCoeff (Δ (fun x ↦ velocity x t.1))
    (laplacian_contDiff
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).continuous
    (laplacian_isOnePeriodic
      ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le
        (WithTop.coe_le_coe.mpr le_top))
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) k

/-- The open solution's actual Laplacian mode is exactly diagonal Stokes damping. -/
theorem openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openVelocityLaplacianMode solution t k =
      -(torusStokesEigenvalue k : ℂ) • velocityMode velocity k t.1 := by
  rw [openVelocityLaplacianMode]
  rw [vectorSpatialFourierCoeff_laplacian_eq_stokes
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k]
  congr 1
  ext component
  exact (velocityModeComponent_eq_openPeriodicVelocityFourierMode
    solution t k component).symm

/-- The momentum coefficient after restoring the exact pressure-gradient summand which the
strong pointwise momentum equation placed with a minus sign. -/
def pressureFreeMomentumMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  unforcedMomentumMode nu velocity pressure k t.1 +
    openPressureGradientMode solution t k

/-- **Strongest checked pressure-free vorticity modal ODE.**  The derivative is first obtained
from the actual pointwise momentum equation.  The separately derived pressure-gradient
coefficient is then restored, and its frequency curl vanishes exactly. -/
theorem openPeriodicSolutionOn_hasDerivAt_vorticityMode_pressureFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (fun τ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
      (frequencyCurlMultiplier k (pressureFreeMomentumMode solution t k)) t.1 := by
  have hderiv :=
    openPeriodicSolutionOn_hasDerivAt_frequencyCurlVelocityMode_unforced
      solution t.2 k
  have hpressure :=
    openPeriodicSolutionOn_frequencyCurl_pressureGradientMode_eq_zero solution t k
  convert hderiv using 1
  rw [pressureFreeMomentumMode]
  change frequencyCurlMultiplierRealCLM k
      (unforcedMomentumMode nu velocity pressure k t.1 +
        openPressureGradientMode solution t k) =
    frequencyCurlMultiplier k
      (unforcedMomentumMode nu velocity pressure k t.1)
  rw [map_add]
  have hpressure' :
      frequencyCurlMultiplierRealCLM k
        (openPressureGradientMode solution t k) = 0 := by
    exact hpressure
  rw [hpressure', add_zero]
  rfl

section Audit

#print axioms diagonalSecondDerivativeFourierMode_eq_multiplier_sq
#print axioms vectorSpatialFourierCoeff_laplacian_eq_stokes
#print axioms periodicTorusLift_isCoordinateDerivative_scalar
#print axioms scalarDirectionalDerivativeFourierMode_eq_multiplier
#print axioms vectorSpatialFourierCoeff_gradient_eq_frequency
#print axioms frequencyCurlMultiplier_gradientFourierMode_eq_zero
#print axioms openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes
#print axioms openPeriodicSolutionOn_frequencyCurl_pressureGradientMode_eq_zero
#print axioms openPeriodicSolutionOn_hasDerivAt_vorticityMode_pressureFree

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols
