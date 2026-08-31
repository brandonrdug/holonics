import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceFourier
import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction

/-!
# The complete two-point coherence carrier is absolutely summable

**[proved-derived]** The six addressed Jacobian entries which form curl are absolutely summable
on every strict interior slice.  Their exact curl incidence therefore majorizes the complete
vorticity coefficient population.  Fixed-receiver cross transport preserves summability, giving
one full `ℓ¹` coefficient mass for the literal two-point field
`y ↦ omega(x) × omega(y)`.  Every finite frequency aperture factors through this same carrier, so
the physical stretching estimate no longer pays a mode-count-dependent coherence constant.
-/

noncomputable section

open scoped BigOperators
open Filter

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceFourier

/-- The six Jacobian-entry occurrences from which one vorticity coefficient is assembled. -/
def complexCurlEntryMass (J : ComplexJacobianArray) : ℝ :=
  ‖J 2 1‖ + ‖J 1 2‖ + ‖J 0 2‖ + ‖J 2 0‖ + ‖J 1 0‖ + ‖J 0 1‖

/-- Curl incidence is bounded by the complete mass of its six signed source occurrences. -/
theorem complexVectorL1_complexCurlFromJacobian_le
    (J : ComplexJacobianArray) :
    complexVectorL1 (complexCurlFromJacobian J) ≤ complexCurlEntryMass J := by
  have h0 := norm_sub_le (J 2 1) (J 1 2)
  have h1 := norm_sub_le (J 0 2) (J 2 0)
  have h2 := norm_sub_le (J 1 0) (J 0 1)
  change
    ‖J 2 1 - J 1 2‖ + ‖J 0 2 - J 2 0‖ + ‖J 1 0 - J 0 1‖ ≤
      ‖J 2 1‖ + ‖J 1 2‖ + ‖J 0 2‖ + ‖J 2 0‖ + ‖J 1 0‖ + ‖J 0 1‖
  linarith

/-- Six-entry majorant of one actual vorticity coefficient on an admitted solution slice. -/
def openPeriodicVorticityCurlEntryMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) : ℝ :=
  complexCurlEntryMass (openPeriodicJacobianFourierMode solution t frequency)

/-- The six-entry curl majorant is summable because every actual Jacobian-entry coefficient
population is already absolutely summable. -/
theorem summable_openPeriodicVorticityCurlEntryMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable (openPeriodicVorticityCurlEntryMass solution t) := by
  have h21 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 2 1
  have h12 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 1 2
  have h02 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 0 2
  have h20 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 2 0
  have h10 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 1 0
  have h01 := summable_norm_openPeriodicJacobianFourierMode_entry solution t 0 1
  change Summable (fun frequency : SpatialFrequency ↦
    (((((‖openPeriodicJacobianFourierMode solution t frequency 2 1‖ +
        ‖openPeriodicJacobianFourierMode solution t frequency 1 2‖) +
      ‖openPeriodicJacobianFourierMode solution t frequency 0 2‖) +
      ‖openPeriodicJacobianFourierMode solution t frequency 2 0‖) +
      ‖openPeriodicJacobianFourierMode solution t frequency 1 0‖) +
      ‖openPeriodicJacobianFourierMode solution t frequency 0 1‖))
  exact (((((h21.add h12).add h02).add h20).add h10).add h01)

/-- Exact curl descent from the actual vorticity coefficient to its addressed Jacobian array. -/
theorem openPeriodicVorticityFourierMode_eq_complexCurl
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution t frequency =
      complexCurlFromJacobian (openPeriodicJacobianFourierMode solution t frequency) := by
  exact actualVorticityFourierMode_eq_complexCurl
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) frequency

/-- Each actual vorticity coefficient is bounded by the six-entry summable curl carrier. -/
theorem complexVectorL1_openPeriodicVorticityFourierMode_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) ≤
      openPeriodicVorticityCurlEntryMass solution t frequency := by
  rw [openPeriodicVorticityFourierMode_eq_complexCurl]
  exact complexVectorL1_complexCurlFromJacobian_le _

/-- The full `L¹` population of actual vorticity Fourier coefficients is summable. -/
theorem summable_complexVectorL1_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun frequency : SpatialFrequency ↦
      complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
  refine Summable.of_nonneg_of_le
    (fun frequency ↦ complexVectorL1_nonneg _)
    (fun frequency ↦ complexVectorL1_openPeriodicVorticityFourierMode_le
      solution t frequency)
    (summable_openPeriodicVorticityCurlEntryMass solution t)

/-- The Fourier coefficients of the literal two-point cross-direction field are absolutely
summable for every receiving occurrence. -/
theorem summable_complexVectorL1_mFourierCoeff_openPeriodicCrossDirectionField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    Summable fun frequency : SpatialFrequency ↦
      complexVectorL1
        (UnitAddTorus.mFourierCoeff
          (openPeriodicCrossDirectionField solution t q) frequency) := by
  have hmajorant :=
    (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t).mul_left
      (complexVectorL1 (openPeriodicComplexVorticityAt solution t q))
  refine Summable.of_nonneg_of_le
    (fun frequency ↦ complexVectorL1_nonneg _)
    (fun frequency ↦ ?_)
    hmajorant
  rw [mFourierCoeff_openPeriodicCrossDirectionField]
  exact complexVectorL1_cross_le_mul _ _

/-- Complete absolute coefficient mass of the actual two-point coherence field. -/
def openPeriodicFullCrossDirectionCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : ℝ :=
  ∑' frequency : SpatialFrequency,
    complexVectorL1
      (UnitAddTorus.mFourierCoeff
        (openPeriodicCrossDirectionField solution t q) frequency)

theorem openPeriodicFullCrossDirectionCoefficientMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    0 ≤ openPeriodicFullCrossDirectionCoefficientMass solution t q := by
  unfold openPeriodicFullCrossDirectionCoefficientMass
  exact tsum_nonneg fun frequency ↦ complexVectorL1_nonneg _

/-- Complete absolute coefficient mass of the actual vorticity slice. -/
def openPeriodicFullVorticityCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ :=
  ∑' frequency : SpatialFrequency,
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)

theorem openPeriodicFullVorticityCoefficientMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    0 ≤ openPeriodicFullVorticityCoefficientMass solution t := by
  unfold openPeriodicFullVorticityCoefficientMass
  exact tsum_nonneg fun frequency ↦ complexVectorL1_nonneg _

/-- The complete two-point carrier obeys the exact fixed-receiver capacitance law: its source
population is bounded by receiver magnitude times the complete source-vorticity population. -/
theorem openPeriodicFullCrossDirectionCoefficientMass_le_receiver_mul_vorticityMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullCrossDirectionCoefficientMass solution t q ≤
      complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        openPeriodicFullVorticityCoefficientMass solution t := by
  have hleft :=
    summable_complexVectorL1_mFourierCoeff_openPeriodicCrossDirectionField solution t q
  have hright :=
    (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t).mul_left
      (complexVectorL1 (openPeriodicComplexVorticityAt solution t q))
  unfold openPeriodicFullCrossDirectionCoefficientMass
    openPeriodicFullVorticityCoefficientMass
  calc
    (∑' frequency : SpatialFrequency,
        complexVectorL1
          (UnitAddTorus.mFourierCoeff
            (openPeriodicCrossDirectionField solution t q) frequency)) ≤
        ∑' frequency : SpatialFrequency,
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      exact hleft.tsum_le_tsum (fun frequency ↦ by
        rw [mFourierCoeff_openPeriodicCrossDirectionField]
        exact complexVectorL1_cross_le_mul _ _) hright
    _ = complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        ∑' frequency : SpatialFrequency,
          complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
      rw [tsum_mul_left]

/-- **Uniform aperture law.** Every finite coefficient population factors through one full
coherence carrier, independently of its shape or cardinality. -/
theorem openPeriodicCrossDirectionCoefficientMass_le_full
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    openPeriodicCrossDirectionCoefficientMass solution t q modes ≤
      openPeriodicFullCrossDirectionCoefficientMass solution t q := by
  unfold openPeriodicCrossDirectionCoefficientMass
    openPeriodicFullCrossDirectionCoefficientMass
  exact
    (summable_complexVectorL1_mFourierCoeff_openPeriodicCrossDirectionField
      solution t q).sum_le_tsum modes
        (fun frequency _hfrequency ↦ complexVectorL1_nonneg _)

/-- Frequency cubes of every radius are uniformly controlled by the same complete coherence
mass.  This is the scale-uniform return needed by the full-strain passage. -/
theorem openPeriodicCrossDirectionCoefficientMass_frequencyCube_le_full
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    openPeriodicCrossDirectionCoefficientMass solution t q (frequencyCube radius) ≤
      openPeriodicFullCrossDirectionCoefficientMass solution t q :=
  openPeriodicCrossDirectionCoefficientMass_le_full solution t q (frequencyCube radius)

/-- **[proved-derived; formal-checked]** Physical vortex stretching is bounded at every scale by
one complete two-point coherence mass plus the explicit decaying weighted-`H³` tail.  The
coherence term is now independent of the chosen Fourier aperture. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_fullCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicFullCrossDirectionCoefficientMass solution t q) +
        ((2 * Real.pi) *
            Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  have hfinite :=
    abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_coherenceCoefficients
      solution t q radius
  refine hfinite.trans ?_
  have hmass :=
    openPeriodicCrossDirectionCoefficientMass_frequencyCube_le_full
      solution t q radius
  have hinner := mul_le_mul_of_nonneg_left hmass
    (mul_nonneg
      (norm_nonneg
        ((complexDot (openPeriodicComplexVorticityAt solution t q)
          (openPeriodicComplexVorticityAt solution t q))⁻¹))
      (complexVectorL1_nonneg (openPeriodicComplexVorticityAt solution t q)))
  have hmain := mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3)
      (sq_nonneg (complexVectorL1 (openPeriodicComplexVorticityAt solution t q))))
  exact add_le_add_left hmain _

/-- The explicit reciprocal scale in the Jacobian reconstruction fibre converges to zero. -/
theorem tendsto_jacobianTailScale_atTop :
    Tendsto jacobianTailScale atTop (nhds 0) := by
  have hbase : Tendsto (fun radius : ℕ ↦ (radius : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hdecay :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp hbase
  refine hdecay.congr' ?_
  filter_upwards [] with radius
  simp [jacobianTailScale, Function.comp_apply]

/-- The remaining full-strain reconstruction fibre, kept as one addressed receiver quantity. -/
def openPeriodicCoherenceFourierTail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (radius : ℕ) : ℝ :=
  ((2 * Real.pi) *
      Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
        ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
    complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2

/-- The addressed reconstruction fibre disappears in the complete-frequency receiver. -/
theorem tendsto_openPeriodicCoherenceFourierTail_atTop
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    Tendsto (openPeriodicCoherenceFourierTail solution t q) atTop (nhds 0) := by
  let response : ℝ → ℝ := fun scale ↦
    ((2 * Real.pi) *
        Real.sqrt (scale * jacobianTailLatticeMass) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) *
      complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2
  have hresponse : Continuous response := by
    dsimp [response]
    fun_prop
  have hzero : response 0 = 0 := by
    simp [response]
  have htransport := hresponse.continuousAt.tendsto.comp tendsto_jacobianTailScale_atTop
  change Tendsto (response ∘ jacobianTailScale) atTop (nhds 0)
  simpa only [hzero] using htransport

/-- **Complete-frequency physical receiver.**  Passing through the vanishing reconstruction
fibre removes the radius entirely: physical vortex stretching is bounded directly by the full
absolute coefficient mass of the actual two-point coherence field. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_fullCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullCrossDirectionCoefficientMass solution t q) := by
  have hlimit : Tendsto (fun radius : ℕ ↦
      3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
          (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
                (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
            complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
              openPeriodicFullCrossDirectionCoefficientMass solution t q) +
        openPeriodicCoherenceFourierTail solution t q radius) atTop
      (nhds (3 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 *
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
              (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullCrossDirectionCoefficientMass solution t q))) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_openPeriodicCoherenceFourierTail_atTop solution t q))
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun radius ↦ by
    simpa only [openPeriodicCoherenceFourierTail] using
      abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_fullCoherence
        solution t q radius

section Audit

#print axioms complexVectorL1_complexCurlFromJacobian_le
#print axioms summable_openPeriodicVorticityCurlEntryMass
#print axioms openPeriodicVorticityFourierMode_eq_complexCurl
#print axioms complexVectorL1_openPeriodicVorticityFourierMode_le
#print axioms summable_complexVectorL1_openPeriodicVorticityFourierMode
#print axioms summable_complexVectorL1_mFourierCoeff_openPeriodicCrossDirectionField
#print axioms openPeriodicFullCrossDirectionCoefficientMass_le_receiver_mul_vorticityMass
#print axioms openPeriodicCrossDirectionCoefficientMass_le_full
#print axioms openPeriodicCrossDirectionCoefficientMass_frequencyCube_le_full
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_frequencyCube_le_fullCoherence
#print axioms tendsto_jacobianTailScale_atTop
#print axioms tendsto_openPeriodicCoherenceFourierTail_atTop
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_fullCoherence

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
