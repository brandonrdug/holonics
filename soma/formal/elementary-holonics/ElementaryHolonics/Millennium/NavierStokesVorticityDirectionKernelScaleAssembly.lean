import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionFullStrain
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelCancellation

/-!
# Exact spatial direction cancellation through the complete dyadic Hodge word

**[proved-derived]** One physical dyadic band already factors through the point-to-point
vorticity-direction remainder.  This owner performs the missing finite scale gluing.  The complete
strain is reconstructed exactly from its base, every ordered dyadic spatial cancellation return,
and the retained high-frequency fibre.  The resulting estimate has no coefficient-count term:
its only scale population is the literal kernel-weighted geometric cross coherence.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Symmetric stretching commutes with a finite population indexed by any occurrence type. -/
theorem complexStretchingReading_symmetric_finset_sum
    {ι : Type*} (receiver : ComplexVector) (indices : Finset ι)
    (J : ι → ComplexMatrix3) :
    complexStretchingReading receiver
        (symmetricComplexJacobianPart (∑ index ∈ indices, J index)) =
      ∑ index ∈ indices,
        complexStretchingReading receiver (symmetricComplexJacobianPart (J index)) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, Finset.sum_insert hindex,
        symmetricComplexJacobianPart_add, complexStretchingReading_add, ih]

/-- Two fixed receiver factors pass through an arbitrary finite real occurrence population. -/
theorem sum_const_mul_mul
    {ι : Type*} (indices : Finset ι) (f : ι → ℝ) (left right : ℝ) :
    (∑ index ∈ indices, (left * f index) * right) =
      (left * ∑ index ∈ indices, f index) * right := by
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The low-frequency standing retained before the ordered dyadic scale word. -/
def openPeriodicDyadicBaseStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℂ :=
  complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (openPeriodicDyadicHodgeJacobianLowPass solution t 0 q))

/-- The addressed high-frequency reconstruction fibre after a finite dyadic word. -/
def openPeriodicDyadicReconstructionFiberStrainReading
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) : ℂ :=
  complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q))

/-- The complete finite spatial direction-coherence word through `depth` dyadic scales. -/
def openPeriodicDyadicSpatialDirectionCoherenceWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    openPeriodicDyadicSpatialDirectionCoherenceMass solution t q scale

/-- The complete finite spatial cross-coherence word through `depth` dyadic scales. -/
def openPeriodicDyadicSpatialCrossCoherenceWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale

theorem openPeriodicDyadicSpatialDirectionCoherenceWord_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    0 ≤ openPeriodicDyadicSpatialDirectionCoherenceWord solution t q depth := by
  unfold openPeriodicDyadicSpatialDirectionCoherenceWord
  apply Finset.sum_nonneg
  intro scale _hscale
  exact openPeriodicDyadicSpatialDirectionCoherenceMass_nonneg solution t q scale

theorem openPeriodicDyadicSpatialCrossCoherenceWord_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    0 ≤ openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth := by
  unfold openPeriodicDyadicSpatialCrossCoherenceWord
  apply Finset.sum_nonneg
  intro scale _hscale
  unfold openPeriodicDyadicSpatialCrossCoherenceMass
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (complexVectorL1_nonneg _)

/-- Every band reading in the ordered dyadic word is exactly its spatial direction-remainder
integral. -/
theorem openPeriodicDyadicHodgeStrainWord_eq_spatialDirectionRemainderWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (∑ scale ∈ Finset.range depth,
            openPeriodicDyadicHodgeJacobianBand solution t scale q)) =
      ∑ scale ∈ Finset.range depth,
        ∫ y : SpatialTorus,
          dyadicHodgeStretchingKernelReading scale y
            (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicSpatialDirectionRemainderField solution t q y) := by
  let bands : ℕ → ComplexMatrix3 := fun scale ↦ Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianBand solution t scale q component coordinate
  change complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (∑ scale ∈ Finset.range depth, bands scale)) = _
  rw [complexStretchingReading_symmetric_finset_sum]
  apply Finset.sum_congr rfl
  intro scale _hscale
  exact openPeriodicDyadicHodgeStrainReading_eq_spatialDirectionRemainder
    solution t q scale

/-- **Exact complete spatial scale gluing.**  The full strain is the low-frequency standing,
followed by every spatially cancelled dyadic band, followed by the retained reconstruction fibre.
-/
theorem openPeriodicFullStrainReading_eq_dyadicSpatialDirectionWord_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    openPeriodicFullStrainReading solution t q =
      openPeriodicDyadicBaseStrainReading solution t q +
        (∑ scale ∈ Finset.range depth,
          ∫ y : SpatialTorus,
            dyadicHodgeStretchingKernelReading scale y
              (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicSpatialDirectionRemainderField solution t q y)) +
        openPeriodicDyadicReconstructionFiberStrainReading solution t q depth := by
  rw [openPeriodicFullStrainReading,
    openPeriodicTorusJacobianArraySlice_eq_base_add_sum_dyadicBands_add_fiber]
  let receiver := openPeriodicComplexVorticityAt solution t q
  let base : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 q component coordinate
  let bands : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    (∑ scale ∈ Finset.range depth,
      openPeriodicDyadicHodgeJacobianBand solution t scale q) component coordinate
  let fiber : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q component coordinate
  change complexStretchingReading receiver
    (symmetricComplexJacobianPart (base + bands + fiber)) = _
  rw [symmetricComplexJacobianPart_add, complexStretchingReading_add,
    symmetricComplexJacobianPart_add, complexStretchingReading_add]
  have hword :=
    openPeriodicDyadicHodgeStrainWord_eq_spatialDirectionRemainderWord
      solution t q depth
  change complexStretchingReading receiver (symmetricComplexJacobianPart bands) = _ at hword
  rw [hword]
  rfl

/-- The norm of the complete finite dyadic band population is bounded by the sum of its literal
spatial direction-coherence masses. -/
theorem norm_openPeriodicDyadicHodgeStrainWord_le_spatialDirectionCoherenceWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (∑ scale ∈ Finset.range depth,
            openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      openPeriodicDyadicSpatialDirectionCoherenceWord solution t q depth := by
  let bands : ℕ → ComplexMatrix3 := fun scale ↦ Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianBand solution t scale q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (∑ scale ∈ Finset.range depth, bands scale))‖ ≤ _
  rw [complexStretchingReading_symmetric_finset_sum]
  refine (norm_sum_le _ _).trans ?_
  unfold openPeriodicDyadicSpatialDirectionCoherenceWord
  apply Finset.sum_le_sum
  intro scale _hscale
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart (bands scale))‖ ≤ _
  exact norm_openPeriodicDyadicHodgeStrainReading_le_spatialDirectionCoherenceMass
    solution t q scale

/-- The complete strain is bounded by the base, the exact spatial coherence word, and the retained
high-frequency fibre. -/
theorem norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionWord_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      ‖openPeriodicDyadicBaseStrainReading solution t q‖ +
        openPeriodicDyadicSpatialDirectionCoherenceWord solution t q depth +
        ‖openPeriodicDyadicReconstructionFiberStrainReading solution t q depth‖ := by
  have hword :=
    norm_openPeriodicDyadicHodgeStrainWord_le_spatialDirectionCoherenceWord
      solution t q depth
  rw [openPeriodicDyadicHodgeStrainWord_eq_spatialDirectionRemainderWord] at hword
  rw [openPeriodicFullStrainReading_eq_dyadicSpatialDirectionWord_add_fiber]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((norm_add_le _ _).trans (add_le_add le_rfl hword)) le_rfl)

/-- The fixed low-frequency standing has the existing exact scale-zero physical bound. -/
theorem norm_openPeriodicDyadicBaseStrainReading_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicDyadicBaseStrainReading solution t q‖ ≤
      (81 * criticalVorticityRate solution t.1) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  unfold openPeriodicDyadicBaseStrainReading
  let base : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart base)‖ ≤ _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  refine (norm_complexStretchingReading_le _ _).trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change ‖openPeriodicDyadicHodgeJacobianLowPass solution t 0 q‖ ≤ _
  rw [openPeriodicDyadicHodgeJacobianLowPass_zero]
  exact norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le solution t q

/-- The remaining high-frequency reading retains exactly the established coefficient tail. -/
theorem norm_openPeriodicDyadicReconstructionFiberStrainReading_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    ‖openPeriodicDyadicReconstructionFiberStrainReading solution t q depth‖ ≤
      (2 * openPeriodicJacobianCoefficientTailMass solution t
          (frequencyCube (dyadicHodgeInnerCutoff depth))) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  unfold openPeriodicDyadicReconstructionFiberStrainReading
  let fiber : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart fiber)‖ ≤ _
  rw [complexStretchingReading_symmetricComplexJacobianPart]
  refine (norm_complexStretchingReading_le _ _).trans ?_
  change ‖openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q‖ *
    complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 ≤ _
  exact mul_le_mul_of_nonneg_right
    (norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_two_mul_tailMass
      solution t depth q) (sq_nonneg _)

/-- **Full dyadic spatial-coherence estimate.**  The coefficient-count aperture has disappeared;
the only finite-scale population is the exact geometric direction word. -/
theorem norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        openPeriodicDyadicSpatialDirectionCoherenceWord solution t q depth +
        (2 * openPeriodicJacobianCoefficientTailMass solution t
            (frequencyCube (dyadicHodgeInnerCutoff depth))) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  exact (norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionWord_add_fiber
    solution t q depth).trans
      (add_le_add
        (add_le_add (norm_openPeriodicDyadicBaseStrainReading_le solution t q) le_rfl)
        (norm_openPeriodicDyadicReconstructionFiberStrainReading_le solution t q depth))

/-- On a nonzero receiver chart the complete dyadic band population factors through the summed
oriented spatial cross-coherence word. -/
theorem norm_openPeriodicDyadicHodgeStrainWord_le_spatialCrossCoherenceWord
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart
          (∑ scale ∈ Finset.range depth,
            openPeriodicDyadicHodgeJacobianBand solution t scale q))‖ ≤
      (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  let bands : ℕ → ComplexMatrix3 := fun scale ↦ Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianBand solution t scale q component coordinate
  change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
    (symmetricComplexJacobianPart
      (∑ scale ∈ Finset.range depth, bands scale))‖ ≤ _
  rw [complexStretchingReading_symmetric_finset_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ scale ∈ Finset.range depth,
        ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
          (symmetricComplexJacobianPart
            (openPeriodicDyadicHodgeJacobianBand solution t scale q))‖) ≤
      ∑ scale ∈ Finset.range depth,
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
      apply Finset.sum_le_sum
      intro scale _hscale
      change ‖complexStretchingReading (openPeriodicComplexVorticityAt solution t q)
        (symmetricComplexJacobianPart (bands scale))‖ ≤ _
      exact norm_openPeriodicDyadicHodgeStrainReading_le_spatialCrossCoherenceMass
        solution t q scale hvorticity
    _ = (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
      simpa only [openPeriodicDyadicSpatialCrossCoherenceWord, mul_assoc] using
        sum_const_mul_mul (Finset.range depth)
          (fun scale ↦ openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale)
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q))
          (complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2)

/-- **Exact assembled geometric bound.**  At a nonzero receiver the full physical strain is
controlled by fixed low standing, the summed spatial cross-coherence word, and the addressed tail.
-/
theorem norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (2 * openPeriodicJacobianCoefficientTailMass solution t
            (frequencyCube (dyadicHodgeInnerCutoff depth))) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hband :=
    norm_openPeriodicDyadicHodgeStrainWord_le_spatialCrossCoherenceWord
      solution t q depth hvorticity
  let receiver := openPeriodicComplexVorticityAt solution t q
  let base : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 q component coordinate
  let bands : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    (∑ scale ∈ Finset.range depth,
      openPeriodicDyadicHodgeJacobianBand solution t scale q) component coordinate
  let fiber : ComplexMatrix3 := Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q component coordinate
  change ‖complexStretchingReading receiver (symmetricComplexJacobianPart bands)‖ ≤ _ at hband
  rw [openPeriodicFullStrainReading,
    openPeriodicTorusJacobianArraySlice_eq_base_add_sum_dyadicBands_add_fiber]
  change ‖complexStretchingReading receiver
    (symmetricComplexJacobianPart (base + bands + fiber))‖ ≤ _
  rw [symmetricComplexJacobianPart_add, complexStretchingReading_add,
    symmetricComplexJacobianPart_add, complexStretchingReading_add]
  exact (norm_add_le _ _).trans
    (add_le_add
      ((norm_add_le _ _).trans
        (add_le_add (norm_openPeriodicDyadicBaseStrainReading_le solution t q) hband))
      (norm_openPeriodicDyadicReconstructionFiberStrainReading_le solution t q depth))

section Audit

#print axioms complexStretchingReading_symmetric_finset_sum
#print axioms openPeriodicDyadicHodgeStrainWord_eq_spatialDirectionRemainderWord
#print axioms openPeriodicFullStrainReading_eq_dyadicSpatialDirectionWord_add_fiber
#print axioms norm_openPeriodicDyadicHodgeStrainWord_le_spatialDirectionCoherenceWord
#print axioms norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionWord_add_fiber
#print axioms norm_openPeriodicDyadicBaseStrainReading_le
#print axioms norm_openPeriodicDyadicReconstructionFiberStrainReading_le
#print axioms norm_openPeriodicFullStrainReading_le_dyadicSpatialDirectionCoherence
#print axioms norm_openPeriodicDyadicHodgeStrainWord_le_spatialCrossCoherenceWord
#print axioms norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
