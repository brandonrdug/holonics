import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# Infinite-depth spatial cross-coherence receiver

**[proved-derived]** The finite spatial Hodge word is now complete.  This owner removes its
remaining dyadic reconstruction aperture.  At every fixed strict-interior slice the coefficient
fibre vanishes along dyadic depth.  If and only if the new geometric scale population is supplied
as a summable constitutive law, its finite words factor through one full spatial cross-coherence
mass and the physical stretching receiver passes to that exact infinite-depth carrier.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-- The exact missing spatial constitutive law at one strict-interior receiver occurrence: the
kernel-weighted cross-coherence population is summable over all dyadic scales. -/
def OpenPeriodicDyadicSpatialCrossCoherenceSummable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : Prop :=
  Summable fun scale : ℕ ↦
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale

/-- The complete spatial cross-coherence mass after all dyadic scales are glued. -/
def openPeriodicFullSpatialCrossCoherenceMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℝ :=
  ∑' scale : ℕ,
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale

theorem openPeriodicFullSpatialCrossCoherenceMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    0 ≤ openPeriodicFullSpatialCrossCoherenceMass solution t q := by
  unfold openPeriodicFullSpatialCrossCoherenceMass
  apply tsum_nonneg
  intro scale
  unfold openPeriodicDyadicSpatialCrossCoherenceMass
  exact integral_nonneg fun y ↦
    mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
      (complexVectorL1_nonneg _)

/-- **Uniform scale theorem.** Every finite ordered cross-coherence word factors through the one
complete spatial carrier, independently of its depth. -/
theorem openPeriodicDyadicSpatialCrossCoherenceWord_le_full
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q)
    (depth : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceWord solution t q depth ≤
      openPeriodicFullSpatialCrossCoherenceMass solution t q := by
  unfold openPeriodicDyadicSpatialCrossCoherenceWord
    openPeriodicFullSpatialCrossCoherenceMass
  exact hsummable.sum_le_tsum (Finset.range depth) fun scale _hscale ↦ by
    unfold openPeriodicDyadicSpatialCrossCoherenceMass
    exact integral_nonneg fun y ↦
      mul_nonneg (dyadicHodgeJacobianKernelPointMass_nonneg scale y)
        (complexVectorL1_nonneg _)

/-- Exact dyadic cutoffs escape every finite spatial-frequency aperture. -/
theorem tendsto_dyadicHodgeInnerCutoff_atTop :
    Tendsto dyadicHodgeInnerCutoff atTop atTop := by
  unfold dyadicHodgeInnerCutoff dyadicRadius
  exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ))

/-- The already proved smooth-slice Fourier response vanishes along the exact Hodge depth word. -/
theorem tendsto_openPeriodicCoherenceFourierTail_dyadic_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    Tendsto (fun depth : ℕ ↦
      openPeriodicCoherenceFourierTail solution t q
        (dyadicHodgeInnerCutoff depth)) atTop (nhds 0) :=
  (tendsto_openPeriodicCoherenceFourierTail_atTop solution t q).comp
    tendsto_dyadicHodgeInnerCutoff_atTop

/-- A named majorant for the high-frequency term in the assembled spatial bound. -/
def openPeriodicDyadicSpatialAssemblyTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) : ℝ :=
  2 * openPeriodicCoherenceFourierTail solution t q
    (dyadicHodgeInnerCutoff depth)

theorem tendsto_openPeriodicDyadicSpatialAssemblyTail_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    Tendsto (openPeriodicDyadicSpatialAssemblyTail solution t q) atTop (nhds 0) := by
  have htail : Tendsto (fun depth : ℕ ↦
      (2 : ℝ) * openPeriodicCoherenceFourierTail solution t q
        (dyadicHodgeInnerCutoff depth)) atTop (nhds ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul
      (tendsto_openPeriodicCoherenceFourierTail_dyadic_atTop solution t q)
  simpa [openPeriodicDyadicSpatialAssemblyTail] using htail

/-- The literal coefficient reconstruction term is bounded by the vanishing named dyadic tail. -/
theorem openPeriodicDyadicCoefficientTailTerm_le_spatialAssemblyTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    (2 * openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (dyadicHodgeInnerCutoff depth))) *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 ≤
      openPeriodicDyadicSpatialAssemblyTail solution t q depth := by
  have htail := openPeriodicJacobianCoefficientTailMass_frequencyCube_le
    solution t (dyadicHodgeInnerCutoff depth)
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2))
    (sq_nonneg (complexVectorL1 (openPeriodicComplexVorticityAt solution t q)))
  exact hscaled.trans_eq (by
    unfold openPeriodicDyadicSpatialAssemblyTail openPeriodicCoherenceFourierTail
    ring)

/-- Every finite assembled spatial estimate factors through the complete cross-coherence mass plus
one tail which vanishes with depth. -/
theorem norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0)
    (depth : ℕ) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        openPeriodicDyadicSpatialAssemblyTail solution t q depth := by
  refine (norm_openPeriodicFullStrainReading_le_dyadicSpatialCrossCoherence
    solution t q depth hvorticity).trans ?_
  have hword := openPeriodicDyadicSpatialCrossCoherenceWord_le_full
    solution t q hsummable depth
  have hfactor :
      0 ≤ ‖(complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
        complexVectorL1 (openPeriodicComplexVorticityAt solution t q) :=
    mul_nonneg (norm_nonneg _) (complexVectorL1_nonneg _)
  have hmiddle := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hword hfactor)
    (sq_nonneg (complexVectorL1 (openPeriodicComplexVorticityAt solution t q)))
  exact add_le_add
    (add_le_add le_rfl hmiddle)
    (openPeriodicDyadicCoefficientTailTerm_le_spatialAssemblyTail solution t q depth)

/-- **Infinite-depth spatial receiver.**  Once the geometric cross population is summable, the
coefficient reconstruction fibre disappears completely. -/
theorem norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    ‖openPeriodicFullStrainReading solution t q‖ ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hlimit : Tendsto (fun depth : ℕ ↦
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        openPeriodicDyadicSpatialAssemblyTail solution t q depth) atTop
      (nhds ((81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_openPeriodicDyadicSpatialAssemblyTail_atTop solution t q)
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun depth ↦
    norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail
      solution t q hsummable hvorticity depth

/-- The infinite-depth result returns to the literal real physical stretching occurrence.  Zero
receiver points close directly; nonzero points use the lossless cross reconstruction. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hsummable : OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      (81 * criticalVorticityRate solution t.1) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  by_cases hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) = 0
  · have htorus : torusVorticityEvolution solution t q = 0 := by
      change vorticityField velocity (euclideanRepresentative q) t.1 = 0
      simpa [vorticityField] using hvorticity
    have hreceiver : openPeriodicComplexVorticityAt solution t q = 0 := by
      rw [openPeriodicComplexVorticityAt_eq_torusComplexification, htorus]
      rfl
    simp [openPeriodicPhysicalVortexStretchingAt, htorus, hreceiver,
      complexVectorL1]
  · rw [← norm_openPeriodicFullStrainReading_eq_abs_physical]
    exact norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence
      solution t q hsummable hvorticity

section Audit

#print axioms openPeriodicDyadicSpatialCrossCoherenceWord_le_full
#print axioms tendsto_dyadicHodgeInnerCutoff_atTop
#print axioms tendsto_openPeriodicCoherenceFourierTail_dyadic_atTop
#print axioms tendsto_openPeriodicDyadicSpatialAssemblyTail_atTop
#print axioms openPeriodicDyadicCoefficientTailTerm_le_spatialAssemblyTail
#print axioms norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence_add_tail
#print axioms norm_openPeriodicFullStrainReading_le_fullSpatialCrossCoherence
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
