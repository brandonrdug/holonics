import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-!
# Spatial kernel cancellation through the canonical vorticity-direction remainder

**[proved-derived]** The direct dyadic Hodge kernel already realizes every band as a physical
torus convolution.  This owner evaluates that kernel through the physical stretching receiver and
proves pointwise that every source component aligned with the receiving vorticity vanishes.  The
actual dyadic strain reading is consequently the integral of the kernel acting on the canonical
point-to-point direction remainder, not on raw vorticity magnitude.  This is the exact spatial
carrier required before a geometric coherence or direction-curvature estimate can act.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- One kernel occurrence acting on one source vorticity vector before integration. -/
def dyadicHodgeJacobianKernelAction
    (scale : ℕ) (y : SpatialTorus) (source : ComplexVector) : ComplexJacobianArray :=
  fun component coordinate ↦
    ∑ input : Fin 3,
      dyadicHodgeJacobianKernelEntry scale component coordinate input y * source input

/-- The pointwise matrix kernel action is exactly the finite Fourier synthesis of the direct
dyadic Hodge multiplier acting on that same source. -/
theorem dyadicHodgeJacobianKernelAction_eq_finiteFourierSynthesis
    (scale : ℕ) (y : SpatialTorus) (source : ComplexVector) :
    dyadicHodgeJacobianKernelAction scale y source =
      finiteFourierSynthesis
        (fun frequency ↦ dyadicHodgeJacobianMode scale frequency source)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) y := by
  funext component coordinate
  unfold dyadicHodgeJacobianKernelAction dyadicHodgeJacobianKernelEntry
    finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let modes := frequencyCube (dyadicHodgeOuterCutoff (scale + 1))
  change
    (∑ input : Fin 3,
      (∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency y *
          ((dyadicHodgeBandWeight scale frequency : ℂ) *
            hodgeJacobianMultiplierEntry frequency component coordinate input)) *
        source input) =
      ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency y *
          dyadicHodgeJacobianMode scale frequency source component coordinate
  calc
    (∑ input : Fin 3,
      (∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency y *
          ((dyadicHodgeBandWeight scale frequency : ℂ) *
            hodgeJacobianMultiplierEntry frequency component coordinate input)) *
        source input) =
      ∑ input : Fin 3, ∑ frequency ∈ modes,
        (UnitAddTorus.mFourier frequency y *
          ((dyadicHodgeBandWeight scale frequency : ℂ) *
            hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          source input := by
      apply Finset.sum_congr rfl
      intro input _hinput
      rw [Finset.sum_mul]
    _ = ∑ frequency ∈ modes, ∑ input : Fin 3,
        (UnitAddTorus.mFourier frequency y *
          ((dyadicHodgeBandWeight scale frequency : ℂ) *
            hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          source input := by
      rw [Finset.sum_comm]
    _ = ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency y *
          dyadicHodgeJacobianMode scale frequency source component coordinate := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      unfold dyadicHodgeJacobianMode
      rw [Pi.smul_apply, Pi.smul_apply, hodgeJacobianMode_eq_sum_multiplierEntry]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      ring

/-- Stretching is complex-linear in the Jacobian occurrence. -/
theorem complexStretchingReading_smul
    (receiver : ComplexVector) (amplitude : ℂ) (J : ComplexJacobianArray) :
    complexStretchingReading receiver (amplitude • J) =
      amplitude * complexStretchingReading receiver J := by
  simp [complexStretchingReading, complexMatrixAction, complexDot, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ]
  ring

/-- Stretching bundled as the continuous-linear receiver through which the kernel integral
factors. -/
def complexStretchingReadingCLM (receiver : ComplexVector) :
    ComplexJacobianArray →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := complexStretchingReading receiver
      map_add' := complexStretchingReading_add receiver
      map_smul' := fun amplitude J ↦ by
        simpa only [RingHom.id_apply, smul_eq_mul] using
          complexStretchingReading_smul receiver amplitude J }

@[simp]
theorem complexStretchingReadingCLM_apply
    (receiver : ComplexVector) (J : ComplexJacobianArray) :
    complexStretchingReadingCLM receiver J = complexStretchingReading receiver J :=
  rfl

/-- The scalar stretching occurrence carried by one physical kernel point. -/
def dyadicHodgeStretchingKernelReading
    (scale : ℕ) (y : SpatialTorus) (receiver source : ComplexVector) : ℂ :=
  complexStretchingReading receiver
    (dyadicHodgeJacobianKernelAction scale y source)

/-- Exact addressed mode expansion of one physical stretching-kernel occurrence. -/
theorem dyadicHodgeStretchingKernelReading_eq_finiteModeSum
    (scale : ℕ) (y : SpatialTorus) (receiver source : ComplexVector) :
    dyadicHodgeStretchingKernelReading scale y receiver source =
      ∑ frequency ∈ frequencyCube (dyadicHodgeOuterCutoff (scale + 1)),
        (UnitAddTorus.mFourier frequency y *
          (dyadicHodgeBandWeight scale frequency : ℂ)) *
            hodgeStrainModeReading frequency receiver source := by
  rw [dyadicHodgeStretchingKernelReading,
    dyadicHodgeJacobianKernelAction_eq_finiteFourierSynthesis]
  unfold finiteFourierSynthesis
  change complexStretchingReadingCLM receiver
      (∑ frequency ∈ frequencyCube (dyadicHodgeOuterCutoff (scale + 1)),
        UnitAddTorus.mFourier frequency y •
          dyadicHodgeJacobianMode scale frequency source) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [dyadicHodgeJacobianMode]
  rw [smul_smul, complexStretchingReadingCLM_apply,
    complexStretchingReading_smul]
  rw [← complexStretchingReading_symmetricComplexJacobianPart receiver
    (hodgeJacobianMode frequency source)]
  rfl

/-- Every pointwise source component aligned with the receiving vorticity is annihilated by the
physical dyadic stretching kernel. -/
theorem dyadicHodgeStretchingKernelReading_aligned_eq_zero
    (scale : ℕ) (y : SpatialTorus) (receiver : ComplexVector) (amplitude : ℂ) :
    dyadicHodgeStretchingKernelReading scale y receiver (amplitude • receiver) = 0 := by
  rw [dyadicHodgeStretchingKernelReading_eq_finiteModeSum]
  simp only [hodgeStrainModeReading_aligned_eq_zero, mul_zero, Finset.sum_const_zero]

/-- Pointwise physical-space direction cancellation.  Unlike coefficientwise projection, the
aligned amplitude may vary independently at every kernel occurrence. -/
theorem dyadicHodgeStretchingKernelReading_sub_aligned
    (scale : ℕ) (y : SpatialTorus) (receiver source : ComplexVector) (amplitude : ℂ) :
    dyadicHodgeStretchingKernelReading scale y receiver
        (source - amplitude • receiver) =
      dyadicHodgeStretchingKernelReading scale y receiver source := by
  rw [dyadicHodgeStretchingKernelReading_eq_finiteModeSum,
    dyadicHodgeStretchingKernelReading_eq_finiteModeSum]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  rw [hodgeStrainModeReading_sub_aligned]

/-- The canonical receiver-orthogonal pointwise remainder leaves the physical kernel reading
unchanged. -/
theorem dyadicHodgeStretchingKernelReading_directionRemainder
    (scale : ℕ) (y : SpatialTorus) (receiver source : ComplexVector) :
    dyadicHodgeStretchingKernelReading scale y receiver
        (receiverDirectionRemainder receiver source) =
      dyadicHodgeStretchingKernelReading scale y receiver source := by
  exact dyadicHodgeStretchingKernelReading_sub_aligned scale y receiver source
    (receiverAlignedAmplitude receiver source)

/-- Complete entrywise mass of the direct dyadic Hodge kernel at one displacement. -/
def dyadicHodgeJacobianKernelPointMass (scale : ℕ) (y : SpatialTorus) : ℝ :=
  ∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
    ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖

theorem dyadicHodgeJacobianKernelPointMass_nonneg
    (scale : ℕ) (y : SpatialTorus) :
    0 ≤ dyadicHodgeJacobianKernelPointMass scale y := by
  unfold dyadicHodgeJacobianKernelPointMass
  positivity

theorem complexVector_coordinate_norm_le_l1
    (source : ComplexVector) (input : Fin 3) :
    ‖source input‖ ≤ complexVectorL1 source := by
  fin_cases input
  · change ‖source 0‖ ≤ ‖source 0‖ + ‖source 1‖ + ‖source 2‖
    nlinarith [norm_nonneg (source 1), norm_nonneg (source 2)]
  · change ‖source 1‖ ≤ ‖source 0‖ + ‖source 1‖ + ‖source 2‖
    nlinarith [norm_nonneg (source 0), norm_nonneg (source 2)]
  · change ‖source 2‖ ≤ ‖source 0‖ + ‖source 1‖ + ‖source 2‖
    nlinarith [norm_nonneg (source 0), norm_nonneg (source 1)]

/-- Matrix action at one displacement is controlled by the complete local kernel population and
the source direction-remainder magnitude. -/
theorem norm_dyadicHodgeJacobianKernelAction_le
    (scale : ℕ) (y : SpatialTorus) (source : ComplexVector) :
    ‖dyadicHodgeJacobianKernelAction scale y source‖ ≤
      dyadicHodgeJacobianKernelPointMass scale y * complexVectorL1 source := by
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (complexVectorL1_nonneg source))]
  intro component
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (complexVectorL1_nonneg source))]
  intro coordinate
  unfold dyadicHodgeJacobianKernelAction
  calc
    ‖∑ input : Fin 3,
        dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          source input‖ ≤
      ∑ input : Fin 3,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          source input‖ := norm_sum_le _ _
    _ = ∑ input : Fin 3,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖ *
          ‖source input‖ := by
      apply Finset.sum_congr rfl
      intro input _hinput
      rw [norm_mul]
    _ ≤ ∑ input : Fin 3,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖ *
          complexVectorL1 source := by
      apply Finset.sum_le_sum
      intro input _hinput
      exact mul_le_mul_of_nonneg_left
        (complexVector_coordinate_norm_le_l1 source input) (norm_nonneg _)
    _ = (∑ input : Fin 3,
        ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) *
          complexVectorL1 source := by
      rw [Finset.sum_mul]
    _ ≤ dyadicHodgeJacobianKernelPointMass scale y * complexVectorL1 source := by
      apply mul_le_mul_of_nonneg_right _ (complexVectorL1_nonneg source)
      unfold dyadicHodgeJacobianKernelPointMass
      have hcoordinate :
          (∑ input : Fin 3,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) ≤
            ∑ coordinate' : Fin 3, ∑ input : Fin 3,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate' input y‖ :=
        Finset.single_le_sum
          (f := fun coordinate' : Fin 3 ↦ ∑ input : Fin 3,
            ‖dyadicHodgeJacobianKernelEntry scale component coordinate' input y‖)
          (fun coordinate' _hcoordinate' ↦
            Finset.sum_nonneg fun input _hinput ↦ norm_nonneg _)
          (Finset.mem_univ coordinate)
      have hcomponent :
          (∑ coordinate' : Fin 3, ∑ input : Fin 3,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate' input y‖) ≤
            ∑ component' : Fin 3, ∑ coordinate' : Fin 3, ∑ input : Fin 3,
              ‖dyadicHodgeJacobianKernelEntry scale component' coordinate' input y‖ :=
        Finset.single_le_sum
          (f := fun component' : Fin 3 ↦ ∑ coordinate' : Fin 3, ∑ input : Fin 3,
            ‖dyadicHodgeJacobianKernelEntry scale component' coordinate' input y‖)
          (fun component' _hcomponent' ↦
            Finset.sum_nonneg fun coordinate' _hcoordinate' ↦
              Finset.sum_nonneg fun input _hinput ↦ norm_nonneg _)
          (Finset.mem_univ component)
      exact hcoordinate.trans hcomponent

/-- One physical kernel reading is bounded by kernel population, source remainder, and the two
receiving-vorticity incidences in the quadratic stretching receiver. -/
theorem norm_dyadicHodgeStretchingKernelReading_le
    (scale : ℕ) (y : SpatialTorus) (receiver source : ComplexVector) :
    ‖dyadicHodgeStretchingKernelReading scale y receiver source‖ ≤
      dyadicHodgeJacobianKernelPointMass scale y * complexVectorL1 source *
        complexVectorL1 receiver ^ 2 := by
  exact (norm_complexStretchingReading_le receiver
    (dyadicHodgeJacobianKernelAction scale y source)).trans
      (mul_le_mul_of_nonneg_right
        (norm_dyadicHodgeJacobianKernelAction_le scale y source)
        (sq_nonneg (complexVectorL1 receiver)))

/-- The continuous matrix-valued integrand whose Bochner integral is the existing direct dyadic
kernel convolution. -/
def dyadicHodgeJacobianKernelActionField
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector)) (q : SpatialTorus) :
    C(SpatialTorus, ComplexJacobianArray) where
  toFun := fun y ↦ dyadicHodgeJacobianKernelAction scale y (field (q - y))
  continuous_toFun := by
    unfold dyadicHodgeJacobianKernelAction
    fun_prop

/-- The existing coordinatewise convolution is the Bochner integral of the complete matrix
kernel-action occurrence. -/
theorem dyadicHodgeJacobianKernelConvolution_eq_integral_action
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector)) (q : SpatialTorus) :
    dyadicHodgeJacobianKernelConvolution scale field q =
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelActionField scale field q y := by
  funext component coordinate
  let integrand := dyadicHodgeJacobianKernelActionField scale field q
  let evaluateComponent : ComplexJacobianArray →L[ℂ] ComplexVector :=
    ContinuousLinearMap.proj component
  let evaluateCoordinate : ComplexVector →L[ℂ] ℂ :=
    ContinuousLinearMap.proj coordinate
  let evaluation : ComplexJacobianArray →L[ℂ] ℂ :=
    evaluateCoordinate.comp evaluateComponent
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  unfold dyadicHodgeJacobianKernelConvolution
  change (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          field (q - y) input) =
    evaluation (∫ y : SpatialTorus, integrand y)
  rw [← evaluation.integral_comp_comm hintegrable]
  change (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          field (q - y) input) =
    ∫ y : SpatialTorus, ∑ input : Fin 3,
      dyadicHodgeJacobianKernelEntry scale component coordinate input y *
        field (q - y) input
  rw [integral_finset_sum]
  intro input _hinput
  exact continuousMap_integrable_on_compact
    { toFun := fun y : SpatialTorus ↦
        dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          field (q - y) input
      continuous_toFun := by fun_prop }

/-- Stretching commutes with the physical kernel integral. -/
theorem complexStretchingReading_symmetric_kernelConvolution_eq_integral
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) (receiver : ComplexVector) :
    complexStretchingReading receiver
        (symmetricComplexJacobianPart
          (dyadicHodgeJacobianKernelConvolution scale field q)) =
      ∫ y : SpatialTorus,
        dyadicHodgeStretchingKernelReading scale y receiver (field (q - y)) := by
  let J : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    dyadicHodgeJacobianKernelConvolution scale field q component coordinate
  change complexStretchingReading receiver (symmetricComplexJacobianPart J) = _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  change complexStretchingReadingCLM receiver
    (dyadicHodgeJacobianKernelConvolution scale field q) = _
  rw [dyadicHodgeJacobianKernelConvolution_eq_integral_action]
  let integrand := dyadicHodgeJacobianKernelActionField scale field q
  let L := complexStretchingReadingCLM receiver
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  change L (∫ y : SpatialTorus, integrand y) =
    ∫ y : SpatialTorus, L (integrand y)
  rw [← L.integral_comp_comm hintegrable]

/-- The actual point-to-point direction-remainder field seen from receiver `q`. -/
def openPeriodicSpatialDirectionRemainderField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : C(SpatialTorus, ComplexVector) where
  toFun := fun y ↦
    receiverDirectionRemainder (openPeriodicComplexVorticityAt solution t q)
      (complexTorusVorticitySlice solution t (q - y))
  continuous_toFun := by
    unfold receiverDirectionRemainder receiverAlignedAmplitude complexDot dotProduct
    fun_prop

/-- Kernel-weighted magnitude of the canonical point-to-point direction remainder.  This is a
spatial geometric-difference receiver rather than a Fourier coefficient count. -/
def openPeriodicDyadicSpatialDirectionRemainderMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y *
      complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)

/-- Kernel-weighted oriented cross difference between the receiving vorticity and every source
point.  On the nonzero receiver chart it is a lossless geometric carrier for the remainder. -/
def openPeriodicDyadicSpatialCrossCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    dyadicHodgeJacobianKernelPointMass scale y *
      complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y)))

/-- The exact physical-space coherence mass for one dyadic Hodge band and one receiver. -/
def openPeriodicDyadicSpatialDirectionCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) : ℝ :=
  ∫ y : SpatialTorus,
    ‖dyadicHodgeStretchingKernelReading scale y
      (openPeriodicComplexVorticityAt solution t q)
      (openPeriodicSpatialDirectionRemainderField solution t q y)‖

/-- The exact scalar kernel-coherence mass is bounded by the kernel-weighted canonical direction
remainder and the two receiver incidences of stretching. -/
theorem openPeriodicDyadicSpatialDirectionCoherenceMass_le_remainderMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale ≤
      openPeriodicDyadicSpatialDirectionRemainderMass solution t q scale *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  unfold openPeriodicDyadicSpatialDirectionCoherenceMass
    openPeriodicDyadicSpatialDirectionRemainderMass
  let actionField : C(SpatialTorus, ComplexJacobianArray) := {
    toFun := fun y ↦ dyadicHodgeJacobianKernelAction scale y
      (openPeriodicSpatialDirectionRemainderField solution t q y)
    continuous_toFun := by
      unfold dyadicHodgeJacobianKernelAction
      fun_prop }
  let L := complexStretchingReadingCLM
    (openPeriodicComplexVorticityAt solution t q)
  have hleft' : Integrable (fun y : SpatialTorus ↦ ‖L (actionField y)‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦ ‖L (actionField y)‖
        continuous_toFun := continuous_norm.comp
          (L.continuous.comp actionField.continuous) }
  have hleft : Integrable (fun y : SpatialTorus ↦
      ‖dyadicHodgeStretchingKernelReading scale y
        (openPeriodicComplexVorticityAt solution t q)
        (openPeriodicSpatialDirectionRemainderField solution t q y)‖) := by
    change Integrable (fun y : SpatialTorus ↦ ‖L (actionField y)‖)
    exact hleft'
  have hright : Integrable (fun y : SpatialTorus ↦
      (dyadicHodgeJacobianKernelPointMass scale y *
        complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          (dyadicHodgeJacobianKernelPointMass scale y *
            complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) *
              complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2
        continuous_toFun := by
          unfold dyadicHodgeJacobianKernelPointMass complexVectorL1
          fun_prop }
  calc
    (∫ y : SpatialTorus,
        ‖dyadicHodgeStretchingKernelReading scale y
          (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicSpatialDirectionRemainderField solution t q y)‖) ≤
      ∫ y : SpatialTorus,
        (dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
      exact integral_mono hleft hright fun y ↦
        norm_dyadicHodgeStretchingKernelReading_le scale y
          (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicSpatialDirectionRemainderField solution t q y)
    _ = (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
      rw [integral_mul_const]

/-- On every nonzero physical receiver chart, the kernel-weighted canonical remainder factors
through the oriented point-to-point cross population. -/
theorem openPeriodicDyadicSpatialDirectionRemainderMass_le_crossCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    openPeriodicDyadicSpatialDirectionRemainderMass solution t q scale ≤
      ‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale := by
  have hreceiver := openPeriodicComplexVorticityAt_self_ne_zero solution t q hvorticity
  unfold openPeriodicDyadicSpatialDirectionRemainderMass
    openPeriodicDyadicSpatialCrossCoherenceMass
  let factor : ℝ :=
    ‖(complexDot (openPeriodicComplexVorticityAt solution t q)
      (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q)
  have hleft : Integrable (fun y : SpatialTorus ↦
      dyadicHodgeJacobianKernelPointMass scale y *
        complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          dyadicHodgeJacobianKernelPointMass scale y *
            complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)
        continuous_toFun := by
          unfold dyadicHodgeJacobianKernelPointMass complexVectorL1
          fun_prop }
  have hright : Integrable (fun y : SpatialTorus ↦
      factor *
        (dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1
            (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
              (complexTorusVorticitySlice solution t (q - y))))) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦
          factor *
            (dyadicHodgeJacobianKernelPointMass scale y *
              complexVectorL1
                (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
                  (complexTorusVorticitySlice solution t (q - y))))
        continuous_toFun := by
          unfold factor dyadicHodgeJacobianKernelPointMass complexVectorL1
            receiverCrossDifference complexCross
          fun_prop }
  calc
    (∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1 (openPeriodicSpatialDirectionRemainderField solution t q y)) ≤
      ∫ y : SpatialTorus, factor *
        (dyadicHodgeJacobianKernelPointMass scale y *
          complexVectorL1
            (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
              (complexTorusVorticitySlice solution t (q - y)))) := by
      apply integral_mono hleft hright
      intro y
      have hremainder := complexVectorL1_receiverDirectionRemainder_le_crossDifference
        hreceiver
        (source := complexTorusVorticitySlice solution t (q - y))
      have hkernel := dyadicHodgeJacobianKernelPointMass_nonneg scale y
      dsimp [openPeriodicSpatialDirectionRemainderField]
      calc
        dyadicHodgeJacobianKernelPointMass scale y *
            complexVectorL1
              (receiverDirectionRemainder (openPeriodicComplexVorticityAt solution t q)
                (complexTorusVorticitySlice solution t (q - y))) ≤
          dyadicHodgeJacobianKernelPointMass scale y *
            (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
              (complexVectorL1
                  (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
                    (complexTorusVorticitySlice solution t (q - y))) *
                complexVectorL1 (openPeriodicComplexVorticityAt solution t q))) :=
          mul_le_mul_of_nonneg_left hremainder hkernel
        _ = factor *
            (dyadicHodgeJacobianKernelPointMass scale y *
              complexVectorL1
                (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
                  (complexTorusVorticitySlice solution t (q - y)))) := by
          unfold factor
          ring
    _ = factor *
        ∫ y : SpatialTorus,
          dyadicHodgeJacobianKernelPointMass scale y *
            complexVectorL1
              (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
                (complexTorusVorticitySlice solution t (q - y))) := by
      rw [integral_const_mul]

theorem openPeriodicDyadicSpatialDirectionCoherenceMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    0 ≤ openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale := by
  unfold openPeriodicDyadicSpatialDirectionCoherenceMass
  exact integral_nonneg fun y ↦ norm_nonneg _

/-- **Exact spatial gluing.**  The actual dyadic Hodge strain reading is the physical kernel
integral of the canonical point-to-point vorticity-direction remainder. -/
theorem openPeriodicDyadicHodgeStrainReading_eq_spatialDirectionRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicDyadicHodgeJacobianBand solution t scale q)) =
      ∫ y : SpatialTorus,
        dyadicHodgeStretchingKernelReading scale y
          (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicSpatialDirectionRemainderField solution t q y) := by
  rw [openPeriodicDyadicHodgeJacobianBand_eq_kernelConvolution,
    complexStretchingReading_symmetric_kernelConvolution_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with y
  exact (dyadicHodgeStretchingKernelReading_directionRemainder scale y
    (openPeriodicComplexVorticityAt solution t q)
    (complexTorusVorticitySlice solution t (q - y))).symm

/-- The actual dyadic strain is bounded by its exact physical-space direction-coherence mass. -/
theorem norm_openPeriodicDyadicHodgeStrainReading_le_spatialDirectionCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale := by
  rw [openPeriodicDyadicHodgeStrainReading_eq_spatialDirectionRemainder]
  let actionField : C(SpatialTorus, ComplexJacobianArray) := {
    toFun := fun y ↦ dyadicHodgeJacobianKernelAction scale y
      (openPeriodicSpatialDirectionRemainderField solution t q y)
    continuous_toFun := by
      unfold dyadicHodgeJacobianKernelAction
      fun_prop }
  let L := complexStretchingReadingCLM
    (openPeriodicComplexVorticityAt solution t q)
  have hmajorant : Integrable (fun y : SpatialTorus ↦ ‖L (actionField y)‖) :=
    continuousMap_integrable_on_compact
      { toFun := fun y : SpatialTorus ↦ ‖L (actionField y)‖
        continuous_toFun := continuous_norm.comp
          (L.continuous.comp actionField.continuous) }
  apply norm_integral_le_of_norm_le hmajorant
  filter_upwards [] with y
  exact le_rfl

/-- **Geometric cross receiver for one physical dyadic band.**  On the nonzero receiving chart,
the actual strain occurrence is controlled entirely by the kernel-weighted oriented cross
population between the receiver and all translated source vorticities. -/
theorem norm_openPeriodicDyadicHodgeStrainReading_le_spatialCrossCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (scale : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hreading :=
    norm_openPeriodicDyadicHodgeStrainReading_le_spatialDirectionCoherenceMass
      solution t q scale
  have hremainder :=
    openPeriodicDyadicSpatialDirectionCoherenceMass_le_remainderMass
      solution t q scale
  have hcross :=
    openPeriodicDyadicSpatialDirectionRemainderMass_le_crossCoherenceMass
      solution t q scale hvorticity
  exact hreading.trans (hremainder.trans
    (mul_le_mul_of_nonneg_right hcross
      (sq_nonneg (complexVectorL1 (openPeriodicComplexVorticityAt solution t q)))))

section Audit

#print axioms dyadicHodgeJacobianKernelAction_eq_finiteFourierSynthesis
#print axioms complexStretchingReading_smul
#print axioms dyadicHodgeStretchingKernelReading_eq_finiteModeSum
#print axioms dyadicHodgeStretchingKernelReading_aligned_eq_zero
#print axioms dyadicHodgeStretchingKernelReading_sub_aligned
#print axioms dyadicHodgeStretchingKernelReading_directionRemainder
#print axioms norm_dyadicHodgeJacobianKernelAction_le
#print axioms norm_dyadicHodgeStretchingKernelReading_le
#print axioms dyadicHodgeJacobianKernelConvolution_eq_integral_action
#print axioms complexStretchingReading_symmetric_kernelConvolution_eq_integral
#print axioms openPeriodicDyadicSpatialDirectionCoherenceMass_le_remainderMass
#print axioms openPeriodicDyadicSpatialDirectionRemainderMass_le_crossCoherenceMass
#print axioms openPeriodicDyadicHodgeStrainReading_eq_spatialDirectionRemainder
#print axioms norm_openPeriodicDyadicHodgeStrainReading_le_spatialDirectionCoherenceMass
#print axioms norm_openPeriodicDyadicHodgeStrainReading_le_spatialCrossCoherenceMass

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
