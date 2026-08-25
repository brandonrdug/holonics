import ElementaryHolonics.Millennium.NavierStokesDissipationHodgeInteraction
import ElementaryHolonics.Millennium.NavierStokesTorusCubeIntegral

/-!
# The absorbed Hodge interaction enters the signed enstrophy receiver

**[proved-derived]** Finite dyadic scale gluing is integrated before the depth tends to infinity.
Fubini identifies every raw physical Hodge band with the global interaction population already
controlled by dissipation.  The scale-zero standing is paid by kinetic energy and the exact
weighted reconstruction fibre vanishes.  Positive viscosity therefore reaches the signed
enstrophy rate with one exposed nonlinear remainder: the spatial fourth-power vorticity mass.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesDissipationHodgeEnstrophy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDissipationHodgeInteraction
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPhysicalTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusCubeIntegral
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Continuous torus carriers for the finite depth word -/

/-- One raw dyadic band after the receiver and displacement populations have been retained. -/
def openPeriodicDyadicRawHodgeStretchingCarrier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ℝ) where
  toFun q := ∫ y : SpatialTorus,
    ‖dyadicHodgeStretchingKernelReading scale y
      (complexTorusVorticitySlice solution t q)
      (complexTorusVorticitySlice solution t (q - y))‖
  continuous_toFun := by
    simpa only [Measure.restrict_univ] using
      continuous_parametric_integral_of_continuous
        (μ := (volume : Measure SpatialTorus)) (s := Set.univ) (by
          unfold dyadicHodgeStretchingKernelReading dyadicHodgeJacobianKernelAction
            complexStretchingReading complexDot dotProduct complexMatrixAction
            Matrix.mulVec dyadicHodgeJacobianKernelEntry
          fun_prop) isCompact_univ

/-- The raw physical band is exactly the earlier direction-remainder coherence mass: aligned
cancellation changes the source chart but not the reading. -/
theorem openPeriodicDyadicRawHodgeStretchingCarrier_eq_directionCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (scale : ℕ) :
    openPeriodicDyadicRawHodgeStretchingCarrier solution t scale q =
      openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale := by
  unfold openPeriodicDyadicRawHodgeStretchingCarrier
    openPeriodicDyadicSpatialDirectionCoherenceMass
  apply integral_congr_ae
  filter_upwards [] with y
  apply congrArg norm
  simpa using (dyadicHodgeStretchingKernelReading_directionRemainder scale y
    (openPeriodicComplexVorticityAt solution t q)
    (complexTorusVorticitySlice solution t (q - y))).symm

/-- Fubini identifies the receiver-first raw band with the displacement-first global mass used by
the dissipation theorem. -/
theorem integral_openPeriodicDyadicRawHodgeStretchingCarrier_eq_globalMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    (∫ q : SpatialTorus,
      openPeriodicDyadicRawHodgeStretchingCarrier solution t scale q) =
      openPeriodicDyadicDissipationHodgeStretchingMass solution t scale := by
  let integrand : C(SpatialTorus × SpatialTorus, ℝ) := {
    toFun := fun z ↦
      ‖dyadicHodgeStretchingKernelReading scale z.2
        (complexTorusVorticitySlice solution t z.1)
        (complexTorusVorticitySlice solution t (z.1 - z.2))‖
    continuous_toFun := by
      unfold dyadicHodgeStretchingKernelReading dyadicHodgeJacobianKernelAction
        complexStretchingReading complexDot dotProduct complexMatrixAction
        Matrix.mulVec dyadicHodgeJacobianKernelEntry
      fun_prop }
  have hintegrable : Integrable integrand :=
    continuousMap_integrable_on_compact integrand
  unfold openPeriodicDyadicRawHodgeStretchingCarrier
    openPeriodicDyadicDissipationHodgeStretchingMass
  exact integral_integral_swap hintegrable

/-- The continuous norm of the fixed scale-zero strain standing. -/
def openPeriodicDyadicBaseStrainNormCarrier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, ℝ) where
  toFun q := ‖complexStretchingReading (complexTorusVorticitySlice solution t q)
    (symmetricComplexJacobianPart
      (openPeriodicDyadicHodgeJacobianLowPass solution t 0 q))‖
  continuous_toFun := by
    unfold complexStretchingReading symmetricComplexJacobianPart complexMatrixAction
      complexDot dotProduct Matrix.mulVec openPeriodicDyadicHodgeJacobianLowPass
      openPeriodicSmoothHodgeJacobianLowPass finiteFourierSynthesis
    fun_prop

/-- The integrated scale-zero standing. -/
def openPeriodicDyadicBaseStrainTorusMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∫ q : SpatialTorus, openPeriodicDyadicBaseStrainNormCarrier solution t q

/-- The continuous norm of the retained reconstruction fibre at one finite depth. -/
def openPeriodicDyadicReconstructionFiberNormCarrier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : C(SpatialTorus, ℝ) where
  toFun q := ‖complexStretchingReading (complexTorusVorticitySlice solution t q)
    (symmetricComplexJacobianPart
      (openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q))‖
  continuous_toFun := by
    have hfiber : Continuous (fun q : SpatialTorus ↦
        openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q) := by
      have heq : (fun q : SpatialTorus ↦
          openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q) =
          fun q ↦ openPeriodicTorusJacobianArraySlice solution t q -
            openPeriodicDyadicHodgeJacobianLowPass solution t depth q := by
        funext q
        have hdecomposition :=
          openPeriodicTorusJacobianArraySlice_eq_dyadicLowPass_add_fiber
            solution t depth q
        rw [hdecomposition]
        abel
      rw [heq]
      fun_prop
    unfold complexStretchingReading symmetricComplexJacobianPart complexMatrixAction
      complexDot dotProduct Matrix.mulVec
    fun_prop

/-- The integrated reconstruction fibre at one finite depth. -/
def openPeriodicDyadicReconstructionFiberTorusMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  ∫ q : SpatialTorus,
    openPeriodicDyadicReconstructionFiberNormCarrier solution t depth q

/-- The continuous absolute physical vortex-stretching receiver on the genuine torus. -/
def openPeriodicAbsoluteVortexStretchingCarrier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, ℝ) where
  toFun q := |openPeriodicPhysicalVortexStretchingAt solution t q|
  continuous_toFun := by
    unfold openPeriodicPhysicalVortexStretchingAt openPeriodicTorusJacobianSlice
    fun_prop

/-- The complete absolute physical vortex-stretching population on one torus slice. -/
def openPeriodicAbsoluteVortexStretchingTorusMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : ℝ :=
  ∫ q : SpatialTorus, openPeriodicAbsoluteVortexStretchingCarrier solution t q

/-! ## Finite-depth exact gluing and integration -/

/-- At finite depth, the physical absolute reading is bounded by the scale-zero standing, every
raw dyadic band, and the still-addressed reconstruction fibre. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_rawWord_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      openPeriodicDyadicBaseStrainNormCarrier solution t q +
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicRawHodgeStretchingCarrier solution t scale q) +
        openPeriodicDyadicReconstructionFiberNormCarrier solution t depth q := by
  rw [← norm_openPeriodicFullStrainReading_eq_abs_physical]
  have hsource := norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionWord_add_fiber
    solution t q depth
  simpa [openPeriodicDyadicBaseStrainNormCarrier,
    openPeriodicDyadicReconstructionFiberNormCarrier,
    openPeriodicDyadicSpatialDirectionCoherenceWord,
    openPeriodicDyadicRawHodgeStretchingCarrier_eq_directionCoherenceMass]
    using hsource

/-- Integrating the finite word preserves all addressed scale populations. -/
theorem openPeriodicAbsoluteVortexStretchingTorusMass_le_finiteRawWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicAbsoluteVortexStretchingTorusMass solution t ≤
      openPeriodicDyadicBaseStrainTorusMass solution t +
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) +
        openPeriodicDyadicReconstructionFiberTorusMass solution t depth := by
  let left := openPeriodicAbsoluteVortexStretchingCarrier solution t
  let base := openPeriodicDyadicBaseStrainNormCarrier solution t
  let band := fun scale ↦ openPeriodicDyadicRawHodgeStretchingCarrier solution t scale
  let fiber := openPeriodicDyadicReconstructionFiberNormCarrier solution t depth
  have hleft : Integrable left := continuousMap_integrable_on_compact left
  have hbase : Integrable base := continuousMap_integrable_on_compact base
  have hband : ∀ scale : ℕ, Integrable (band scale) :=
    fun scale ↦ continuousMap_integrable_on_compact (band scale)
  have hfiber : Integrable fiber := continuousMap_integrable_on_compact fiber
  have hsum : Integrable (fun q : SpatialTorus ↦
      ∑ scale ∈ Finset.range depth, band scale q) :=
    integrable_finset_sum (Finset.range depth) fun scale _ ↦ hband scale
  unfold openPeriodicAbsoluteVortexStretchingTorusMass
    openPeriodicDyadicBaseStrainTorusMass
    openPeriodicDyadicReconstructionFiberTorusMass
  calc
    (∫ q : SpatialTorus, left q) ≤
      ∫ q : SpatialTorus,
        base q + (∑ scale ∈ Finset.range depth, band scale q) + fiber q := by
      apply integral_mono hleft
      · exact (hbase.add
          (integrable_finset_sum (Finset.range depth) fun scale _ ↦ hband scale)).add hfiber
      · intro q
        exact abs_openPeriodicPhysicalVortexStretchingAt_le_rawWord_add_fiber
          solution t q depth
    _ = (∫ q : SpatialTorus, base q) +
        (∑ scale ∈ Finset.range depth,
          ∫ q : SpatialTorus, band scale q) +
        ∫ q : SpatialTorus, fiber q := by
      have houter := integral_add (hbase.add hsum) hfiber
      have hinner := integral_add hbase hsum
      have hfinite := integral_finset_sum (Finset.range depth)
        (fun scale _hscale ↦ hband scale)
      calc
        _ = (∫ q : SpatialTorus,
              base q + ∑ scale ∈ Finset.range depth, band scale q) +
            ∫ q : SpatialTorus, fiber q := by
          simpa only [Pi.add_apply] using houter
        _ = ((∫ q : SpatialTorus, base q) +
              ∫ q : SpatialTorus,
                ∑ scale ∈ Finset.range depth, band scale q) +
            ∫ q : SpatialTorus, fiber q := by rw [hinner]
        _ = (∫ q : SpatialTorus, base q) +
              (∑ scale ∈ Finset.range depth,
                ∫ q : SpatialTorus, band scale q) +
            ∫ q : SpatialTorus, fiber q := by rw [hfinite]
    _ = (∫ q : SpatialTorus, base q) +
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) +
        ∫ q : SpatialTorus, fiber q := by
      apply congrArg (fun middle : ℝ ↦
        (∫ q : SpatialTorus, base q) + middle + ∫ q : SpatialTorus, fiber q)
      apply Finset.sum_congr rfl
      intro scale _hscale
      exact integral_openPeriodicDyadicRawHodgeStretchingCarrier_eq_globalMass
        solution t scale

/-! ## Scale-zero and reconstruction-fibre returns -/

/-- The torus square population of actual vorticity is twice the periodic enstrophy. -/
theorem integral_norm_sq_torusVorticityEvolution_eq_two_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    (∫ q : SpatialTorus, ‖torusVorticityEvolution solution t q‖ ^ 2) =
      2 * periodicEnstrophy velocity t.1 := by
  let squareField : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦ ‖torusVorticityEvolution solution t q‖ ^ 2
    continuous_toFun := by fun_prop }
  have hchart := integral_euclideanToSpatialTorus_unitCube squareField
  calc
    (∫ q : SpatialTorus, ‖torusVorticityEvolution solution t q‖ ^ 2) =
        ∫ x in unitCube,
          squareField (euclideanToSpatialTorus x) := by
      simpa [squareField] using hchart.symm
    _ = ∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2 := by
      apply setIntegral_congr_fun
      · unfold unitCube
        exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
          isCompact_Icc |>.measurableSet
      · intro x _hx
        change ‖torusVorticityEvolution solution t (euclideanToSpatialTorus x)‖ ^ 2 =
          ‖vorticityField velocity x t.1‖ ^ 2
        rw [torusVorticityEvolution_projection]
    _ = 2 * periodicEnstrophy velocity t.1 := by
      unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul]
      ring

/-- The complete coordinate-`L¹` square population is controlled by the exact Euclidean
enstrophy receiver. -/
theorem integral_complexVectorL1_sq_complexVorticity_le_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    (∫ q : SpatialTorus,
      complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2) ≤
      18 * periodicEnstrophy velocity t.1 := by
  have hleft : Integrable (fun q : SpatialTorus ↦
      complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2) :=
    continuousMap_integrable_on_compact {
      toFun := fun q : SpatialTorus ↦
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2
      continuous_toFun := by
        unfold complexVectorL1
        fun_prop }
  have hright : Integrable (fun q : SpatialTorus ↦
      9 * ‖torusVorticityEvolution solution t q‖ ^ 2) :=
    continuousMap_integrable_on_compact {
      toFun := fun q : SpatialTorus ↦
        9 * ‖torusVorticityEvolution solution t q‖ ^ 2
      continuous_toFun := by fun_prop }
  calc
    (∫ q : SpatialTorus,
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2) ≤
      ∫ q : SpatialTorus,
        9 * ‖torusVorticityEvolution solution t q‖ ^ 2 := by
      apply integral_mono hleft hright
      intro q
      have hL1 := complexVectorL1_complexOfRealSpace_le_three_norm
        (torusVorticityEvolution solution t q)
      exact (pow_le_pow_left₀ (complexVectorL1_nonneg _) hL1 2).trans_eq (by ring)
    _ = 9 * ∫ q : SpatialTorus,
        ‖torusVorticityEvolution solution t q‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 18 * periodicEnstrophy velocity t.1 := by
      rw [integral_norm_sq_torusVorticityEvolution_eq_two_enstrophy]
      ring

/-- The integrated scale-zero standing is paid by kinetic energy times enstrophy. -/
theorem openPeriodicDyadicBaseStrainTorusMass_le_kineticEnergy_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicDyadicBaseStrainTorusMass solution t ≤
      (26244 * Real.pi) *
        Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
          periodicEnstrophy velocity t.1 := by
  let coefficient :=
    (1458 * Real.pi) * Real.sqrt (2 * periodicKineticEnergy velocity t.1)
  have hcoefficient : 0 ≤ coefficient := by
    dsimp [coefficient]
    positivity
  have hleft : Integrable (openPeriodicDyadicBaseStrainNormCarrier solution t) :=
    continuousMap_integrable_on_compact _
  have hright : Integrable (fun q : SpatialTorus ↦
      coefficient * complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2) :=
    continuousMap_integrable_on_compact {
      toFun := fun q : SpatialTorus ↦
        coefficient * complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2
      continuous_toFun := by
        unfold complexVectorL1
        fun_prop }
  unfold openPeriodicDyadicBaseStrainTorusMass
  calc
    (∫ q : SpatialTorus,
        openPeriodicDyadicBaseStrainNormCarrier solution t q) ≤
      ∫ q : SpatialTorus,
        coefficient * complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
      apply integral_mono hleft hright
      intro q
      simpa [coefficient, openPeriodicDyadicBaseStrainNormCarrier] using
        norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy solution t q
    _ = coefficient * ∫ q : SpatialTorus,
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
      rw [integral_const_mul]
    _ ≤ coefficient * (18 * periodicEnstrophy velocity t.1) :=
      mul_le_mul_of_nonneg_left
        (integral_complexVectorL1_sq_complexVorticity_le_enstrophy solution t)
        hcoefficient
    _ = (26244 * Real.pi) *
        Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
          periodicEnstrophy velocity t.1 := by
      dsimp [coefficient]
      ring

/-- An explicit integrated upper receiver for the finite-depth reconstruction fibre. -/
def openPeriodicIntegratedDyadicFiberUpper
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  2 * ((2 * Real.pi) *
      Real.sqrt (jacobianTailScale (dyadicHodgeInnerCutoff depth) *
        jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
    (∫ q : SpatialTorus,
      complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2)

/-- The retained finite-depth fibre is bounded by the explicit integrated weighted tail. -/
theorem openPeriodicDyadicReconstructionFiberTorusMass_le_upper
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicDyadicReconstructionFiberTorusMass solution t depth ≤
      openPeriodicIntegratedDyadicFiberUpper solution t depth := by
  let explicit := (2 * Real.pi) *
      Real.sqrt (jacobianTailScale (dyadicHodgeInnerCutoff depth) *
        jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖
  have hexplicit : 0 ≤ explicit := by
    dsimp [explicit]
    positivity
  have htail := openPeriodicJacobianCoefficientTailMass_frequencyCube_le
    solution t (dyadicHodgeInnerCutoff depth)
  have hleft : Integrable
      (openPeriodicDyadicReconstructionFiberNormCarrier solution t depth) :=
    continuousMap_integrable_on_compact _
  have hright : Integrable (fun q : SpatialTorus ↦
      (2 * explicit) *
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2) :=
    continuousMap_integrable_on_compact {
      toFun := fun q : SpatialTorus ↦
        (2 * explicit) *
          complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2
      continuous_toFun := by
        unfold complexVectorL1
        fun_prop }
  unfold openPeriodicDyadicReconstructionFiberTorusMass
  calc
    (∫ q : SpatialTorus,
        openPeriodicDyadicReconstructionFiberNormCarrier solution t depth q) ≤
      ∫ q : SpatialTorus,
        (2 * explicit) *
          complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
      apply integral_mono hleft hright
      intro q
      have hfiber := norm_openPeriodicDyadicReconstructionFiberStrainReading_le
        solution t q depth
      calc
        openPeriodicDyadicReconstructionFiberNormCarrier solution t depth q ≤
          (2 * openPeriodicJacobianCoefficientTailMass solution t
            (frequencyCube (dyadicHodgeInnerCutoff depth))) *
              complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
          simpa [openPeriodicDyadicReconstructionFiberNormCarrier] using hfiber
        _ ≤ (2 * explicit) *
              complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = (2 * explicit) * ∫ q : SpatialTorus,
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2 := by
      rw [integral_const_mul]
    _ = openPeriodicIntegratedDyadicFiberUpper solution t depth := by
      unfold openPeriodicIntegratedDyadicFiberUpper
      dsimp [explicit]

/-- The exact integrated reconstruction-fibre upper receiver vanishes with dyadic depth. -/
theorem tendsto_openPeriodicIntegratedDyadicFiberUpper_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    Tendsto (openPeriodicIntegratedDyadicFiberUpper solution t) atTop (nhds 0) := by
  let response : ℝ → ℝ := fun scale ↦
    2 * ((2 * Real.pi) * Real.sqrt (scale * jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
      (∫ q : SpatialTorus,
        complexVectorL1 (complexTorusVorticitySlice solution t q) ^ 2)
  have hresponse : Continuous response := by
    dsimp [response]
    fun_prop
  have hscale := tendsto_jacobianTailScale_atTop.comp
    tendsto_dyadicHodgeInnerCutoff_atTop
  have htransport := hresponse.continuousAt.tendsto.comp hscale
  simpa [response, openPeriodicIntegratedDyadicFiberUpper] using htransport

/-! ## Infinite-depth and signed physical returns -/

/-- The absolute physical vortex-stretching population is exactly bounded by the energy-paid base
and the complete raw dyadic Hodge population. -/
theorem openPeriodicAbsoluteVortexStretchingTorusMass_le_base_add_fullHodge
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicAbsoluteVortexStretchingTorusMass solution t ≤
      openPeriodicDyadicBaseStrainTorusMass solution t +
        ∑' scale : ℕ,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale := by
  have hsummable :=
    summable_openPeriodicDyadicDissipationHodgeStretchingMass solution t
      (show 0 < (1 : ℝ) by norm_num)
  have hsum := hsummable.hasSum.tendsto_sum_nat
  have htail := tendsto_openPeriodicIntegratedDyadicFiberUpper_atTop solution t
  have hlimit : Tendsto (fun depth : ℕ ↦
      openPeriodicDyadicBaseStrainTorusMass solution t +
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale) +
        openPeriodicIntegratedDyadicFiberUpper solution t depth) atTop
      (nhds (openPeriodicDyadicBaseStrainTorusMass solution t +
        (∑' scale : ℕ,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale))) := by
    simpa using (tendsto_const_nhds.add hsum).add htail
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun depth ↦
    (openPeriodicAbsoluteVortexStretchingTorusMass_le_finiteRawWord
      solution t depth).trans
        (add_le_add le_rfl
          (openPeriodicDyadicReconstructionFiberTorusMass_le_upper
            solution t depth))

/-- The signed periodic vortex-stretching receiver is bounded by the absolute torus population. -/
theorem periodicVortexStretching_le_absoluteTorusMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    periodicVortexStretching velocity t.1 ≤
      openPeriodicAbsoluteVortexStretchingTorusMass solution t := by
  let signedField : C(SpatialTorus, ℝ) := {
    toFun := fun q ↦ openPeriodicPhysicalVortexStretchingAt solution t q
    continuous_toFun := by
      unfold openPeriodicPhysicalVortexStretchingAt openPeriodicTorusJacobianSlice
      fun_prop }
  let absoluteField : C(SpatialTorus, ℝ) :=
    openPeriodicAbsoluteVortexStretchingCarrier solution t
  have hchart := integral_euclideanToSpatialTorus_unitCube absoluteField
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hsigned : IntegrableOn (fun x : Space ↦
      signedField (euclideanToSpatialTorus x)) unitCube :=
    ((signedField.continuous.comp
        euclideanToSpatialTorus_isOpenQuotientMap.continuous).continuousOn
      |>.integrableOn_compact hcubeCompact)
  have habsolute : IntegrableOn (fun x : Space ↦
      absoluteField (euclideanToSpatialTorus x)) unitCube :=
    ((absoluteField.continuous.comp
        euclideanToSpatialTorus_isOpenQuotientMap.continuous).continuousOn
      |>.integrableOn_compact hcubeCompact)
  calc
    periodicVortexStretching velocity t.1 =
        ∫ x in unitCube, signedField (euclideanToSpatialTorus x) := by
      unfold periodicVortexStretching
      apply setIntegral_congr_fun hcubeMeasurable
      intro x _hx
      dsimp [signedField]
      rw [openPeriodicPhysicalVortexStretchingAt_projection]
    _ ≤ ∫ x in unitCube, absoluteField (euclideanToSpatialTorus x) := by
      apply setIntegral_mono_on hsigned habsolute hcubeMeasurable
      intro x _hx
      exact le_abs_self _
    _ = ∫ q : SpatialTorus, absoluteField q := hchart
    _ = openPeriodicAbsoluteVortexStretchingTorusMass solution t := rfl

/-- **[proved-derived; formal-checked]** The signed vortex-stretching term is paid by the
energy/enstrophy base, half the viscous dissipation, and one exact fourth-power remainder. -/
theorem periodicVortexStretching_le_absorbedHodge
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (hnu : 0 < nu) :
    periodicVortexStretching velocity t.1 ≤
      (26244 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
            periodicEnstrophy velocity t.1 +
        (nu / 2) * periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t := by
  calc
    periodicVortexStretching velocity t.1 ≤
        openPeriodicAbsoluteVortexStretchingTorusMass solution t :=
      periodicVortexStretching_le_absoluteTorusMass solution t
    _ ≤ openPeriodicDyadicBaseStrainTorusMass solution t +
        ∑' scale : ℕ,
          openPeriodicDyadicDissipationHodgeStretchingMass solution t scale :=
      openPeriodicAbsoluteVortexStretchingTorusMass_le_base_add_fullHodge solution t
    _ ≤ (26244 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
            periodicEnstrophy velocity t.1 +
        ((nu / 2) * periodicVorticityDissipation velocity t.1 +
          (27 * totalDyadicHodgeDistanceMoment *
            hodgeDissipationAbsorptionParameter nu / 2) *
              openPeriodicVorticityFourthPowerMass solution t) :=
      add_le_add
        (openPeriodicDyadicBaseStrainTorusMass_le_kineticEnergy_enstrophy solution t)
        (tsum_openPeriodicDyadicDissipationHodgeStretchingMass_le_absorbed
          solution t hnu)
    _ = (26244 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
            periodicEnstrophy velocity t.1 +
        (nu / 2) * periodicVorticityDissipation velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t := by ring

/-- **[proved-derived; formal-checked]** The actual signed enstrophy-rate receiver retains half of
the viscous dissipation with the correct negative orientation.  The only new nonlinear face is the
spatial fourth-power vorticity mass. -/
theorem periodicEnstrophyRate_le_absorbedHodge
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (hnu : 0 < nu) :
    periodicEnstrophyRate nu force velocity t.1 ≤
      -(nu / 2) * periodicVorticityDissipation velocity t.1 +
        (26244 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
            periodicEnstrophy velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t +
        periodicCurlForcingWork force velocity t.1 := by
  unfold periodicEnstrophyRate
  have hstretching := periodicVortexStretching_le_absorbedHodge solution t hnu
  calc
    -nu * periodicVorticityDissipation velocity t.1 +
        periodicVortexStretching velocity t.1 +
          periodicCurlForcingWork force velocity t.1 ≤
      -nu * periodicVorticityDissipation velocity t.1 +
        ((26244 * Real.pi) *
            Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
              periodicEnstrophy velocity t.1 +
          (nu / 2) * periodicVorticityDissipation velocity t.1 +
          (27 * totalDyadicHodgeDistanceMoment *
            hodgeDissipationAbsorptionParameter nu / 2) *
              openPeriodicVorticityFourthPowerMass solution t) +
        periodicCurlForcingWork force velocity t.1 := by
      gcongr
    _ = -(nu / 2) * periodicVorticityDissipation velocity t.1 +
        (26244 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
            periodicEnstrophy velocity t.1 +
        (27 * totalDyadicHodgeDistanceMoment *
          hodgeDissipationAbsorptionParameter nu / 2) *
            openPeriodicVorticityFourthPowerMass solution t +
        periodicCurlForcingWork force velocity t.1 := by ring

section Audit

#print axioms openPeriodicDyadicRawHodgeStretchingCarrier_eq_directionCoherenceMass
#print axioms integral_openPeriodicDyadicRawHodgeStretchingCarrier_eq_globalMass
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_rawWord_add_fiber
#print axioms openPeriodicAbsoluteVortexStretchingTorusMass_le_finiteRawWord
#print axioms integral_norm_sq_torusVorticityEvolution_eq_two_enstrophy
#print axioms integral_complexVectorL1_sq_complexVorticity_le_enstrophy
#print axioms openPeriodicDyadicBaseStrainTorusMass_le_kineticEnergy_enstrophy
#print axioms openPeriodicDyadicReconstructionFiberTorusMass_le_upper
#print axioms tendsto_openPeriodicIntegratedDyadicFiberUpper_atTop
#print axioms openPeriodicAbsoluteVortexStretchingTorusMass_le_base_add_fullHodge
#print axioms periodicVortexStretching_le_absoluteTorusMass
#print axioms periodicVortexStretching_le_absorbedHodge
#print axioms periodicEnstrophyRate_le_absorbedHodge

end Audit

end Soma.Holonics.Millennium.NavierStokesDissipationHodgeEnstrophy
