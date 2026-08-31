import ElementaryHolonics.Millennium.NavierStokesH2StorageDissipationPayment
import ElementaryHolonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
import ElementaryHolonics.Millennium.NavierStokesH3LerayBilinear
import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionBaseEnergy

/-!
# A fixed low output of the actual projected source is paid by kinetic energy

**[proved-derived; formal-checked]**  Incompressibility moves the derivative in each actual
Fourier interaction from the transported frequency `k - p` to the fixed output frequency `k`:

`u_p · (k - p) = u_p · k`.

The resulting fixed-output convolution is an `ell^2 * ell^2` pairing.  Componentwise Parseval
therefore pays its complete parent population by the ordinary kinetic energy of the same velocity
slice; the unforced energy law then moves that payment to the admitted initial trace.  The exact
unit-torus character scale and the standing coordinate-`L1` Leray constant remain visible.

This estimate is useful only after the output frequency is genuinely fixed (or selected from a
finite low population).  It gives no summable bound over comparable or high output tails and makes
no terminal-time, continuation, or solution claim.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectedSourceLowOutputBound

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPhysicalFourierH2ProductionBridge
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ClockedTriadNormalForm
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## The complete interaction population before the fixed-output rotation -/

/-- The complete `H3` convolution is the `tsum` of its addressed advective interactions. -/
theorem h3AdvectiveConvolution_coefficient_eq_tsum_complexAdvectiveInteraction
    (state : PeriodicVectorSobolevThree)
    (hstate : HasAbsolutelySummableComponents state)
    (frequency : SpatialFrequency) (output : Fin 3) :
    h3AdvectiveConvolution state state output frequency =
      ∑' parent : SpatialFrequency,
        complexAdvectiveInteraction parent (frequency - parent)
          (fun component ↦ (state component).1 parent)
          (fun component ↦ (state component).1 (frequency - parent)) output := by
  have hterms : ∀ coordinate ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun parent : SpatialFrequency ↦
        (state coordinate).1 parent *
          periodicSobolevThreeDerivative coordinate
            (state output) (frequency - parent) := by
    intro coordinate _hcoordinate
    apply Summable.of_norm
    have hbound := (hstate coordinate).mul_right
      ‖periodicSobolevThreeDerivative coordinate (state output)‖
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun parent ↦ ?_) hbound
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (periodicSobolevThreeDerivative coordinate (state output))
        (frequency - parent))
      (norm_nonneg _)
  rw [h3AdvectiveConvolution_apply hstate]
  simp_rw [← periodicSobolevThreeDerivative_apply]
  rw [← Summable.tsum_finsetSum hterms]
  apply tsum_congr
  intro parent
  unfold complexAdvectiveInteraction
  simp only [complexDot, dotProduct, smul_eq_mul, Pi.smul_apply,
    complexFrequencyVector, periodicSobolevThreeDerivative_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  ring

/-- Incompressibility rotates one transported derivative to the fixed output frequency. -/
theorem complexAdvectiveInteraction_eq_fixedOutput_of_divergenceFree
    (parent frequency : SpatialFrequency)
    (advecting transported : ComplexVector)
    (hdivergence :
      complexDot (complexFrequencyVector parent) advecting = 0) :
    complexAdvectiveInteraction parent (frequency - parent) advecting transported =
      (unitTorusCurlScale *
        complexDot (complexFrequencyVector frequency) advecting) • transported := by
  rw [complexAdvectiveInteraction_eq_unitTorusCurlScale]
  congr 2
  have hfrequency :
      complexFrequencyVector (frequency - parent) =
        complexFrequencyVector frequency - complexFrequencyVector parent := by
    change complexFrequencyEmbedding (frequency - parent) =
      complexFrequencyEmbedding frequency - complexFrequencyEmbedding parent
    exact map_sub complexFrequencyEmbedding frequency parent
  rw [hfrequency]
  change dotProduct
      (complexFrequencyVector frequency - complexFrequencyVector parent) advecting = _
  rw [sub_dotProduct]
  exact sub_eq_self.mpr hdivergence

/-! ## The `ell^2` carrier of the vector `L1` coefficient mass -/

/-- The complete vector-`L1` coefficient section, retained as a genuine Fourier `ell^2` object. -/
def vectorCoefficientL1FourierL2
    (state : PeriodicVectorSobolevThree) : PeriodicFourierL2 :=
  ⟨fun frequency ↦
      ((complexVectorL1 (fun component ↦ (state component).1 frequency) : ℝ) : ℂ), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hcomponents : Summable fun frequency : SpatialFrequency ↦
        ∑ component : Fin 3, ‖(state component).1 frequency‖ ^ 2 := by
      apply summable_sum
      intro component _hcomponent
      have hcomponent := (lp.memℓp (state component).1).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hcomponent
    refine Summable.of_nonneg_of_le (fun frequency ↦ by positivity)
      (fun frequency ↦ ?_) (hcomponents.mul_left 3)
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexVectorL1_nonneg _), Real.rpow_two]
    exact complexVectorL1_sq_le_three_mul_sum_norm_sq _⟩

/-- Reflecting a vector-`L1` coefficient section through a fixed output preserves `ell^2`. -/
def reflectedVectorCoefficientL1FourierL2
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) :
    PeriodicFourierL2 :=
  ⟨fun parent ↦ vectorCoefficientL1FourierL2 state (frequency - parent), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hsource := (lp.memℓp (vectorCoefficientL1FourierL2 state)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    exact (Equiv.subLeft frequency).summable_iff.mpr hsource⟩

/-- The reflected section has exactly the same Hilbert norm as the source section. -/
theorem norm_reflectedVectorCoefficientL1FourierL2
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) :
    ‖reflectedVectorCoefficientL1FourierL2 state frequency‖ =
      ‖vectorCoefficientL1FourierL2 state‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (reflectedVectorCoefficientL1FourierL2 state frequency)
  have hright := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (vectorCoefficientL1FourierL2 state)
  have hsum :
      (∑' parent : SpatialFrequency,
          ‖reflectedVectorCoefficientL1FourierL2 state frequency parent‖ ^ 2) =
        ∑' parent : SpatialFrequency,
          ‖vectorCoefficientL1FourierL2 state parent‖ ^ 2 := by
    rw [← (Equiv.subLeft frequency).tsum_eq]
    simp [reflectedVectorCoefficientL1FourierL2]
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at hleft hright
  rw [hsum] at hleft
  nlinarith [norm_nonneg (reflectedVectorCoefficientL1FourierL2 state frequency),
    norm_nonneg (vectorCoefficientL1FourierL2 state)]

/-- Infinite convolution Cauchy at one fixed output, before any PDE interpretation. -/
theorem tsum_vectorCoefficientL1_mul_reflected_le_norm_sq
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) :
    (∑' parent : SpatialFrequency,
        complexVectorL1 (fun component ↦ (state component).1 parent) *
          complexVectorL1
            (fun component ↦ (state component).1 (frequency - parent))) ≤
      ‖vectorCoefficientL1FourierL2 state‖ ^ 2 := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hcs := lp.tsum_mul_le_mul_norm' hholder
    (vectorCoefficientL1FourierL2 state)
    (reflectedVectorCoefficientL1FourierL2 state frequency)
  rw [norm_reflectedVectorCoefficientL1FourierL2] at hcs
  simpa only [vectorCoefficientL1FourierL2,
    reflectedVectorCoefficientL1FourierL2, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (complexVectorL1_nonneg _), pow_two] using hcs

/-! ## Fixed-output convolution bound -/

/-- The incompressibly rotated convolution at one fixed output. -/
def fixedOutputVelocityAdvectionMode
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) : ComplexVector :=
  ∑' parent : SpatialFrequency,
    (unitTorusCurlScale *
      complexDot (complexFrequencyVector frequency)
        (fun component ↦ (state component).1 parent)) •
      (fun component ↦ (state component).1 (frequency - parent))

/-- Each rotated term is paid by the exact output frequency and two vector-`L1` occurrences. -/
theorem complexVectorL1_fixedOutputVelocityAdvectionTerm_le
    (state : PeriodicVectorSobolevThree)
    (frequency parent : SpatialFrequency) :
    complexVectorL1
        ((unitTorusCurlScale *
          complexDot (complexFrequencyVector frequency)
            (fun component ↦ (state component).1 parent)) •
          (fun component ↦ (state component).1 (frequency - parent))) ≤
      ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        (complexVectorL1 (fun component ↦ (state component).1 parent) *
          complexVectorL1
            (fun component ↦ (state component).1 (frequency - parent))) := by
  rw [complexVectorL1_smul, norm_mul]
  have hdot := norm_complexDot_le_l1_mul_l1
    (complexFrequencyVector frequency)
    (fun component ↦ (state component).1 parent)
  rw [complexVectorL1_complexFrequencyVector] at hdot
  have htransported := complexVectorL1_nonneg
    (fun component ↦ (state component).1 (frequency - parent))
  calc
    ‖unitTorusCurlScale‖ *
        ‖complexDot (complexFrequencyVector frequency)
          (fun component ↦ (state component).1 parent)‖ *
        complexVectorL1
          (fun component ↦ (state component).1 (frequency - parent)) ≤
      ‖unitTorusCurlScale‖ *
        (frequencyL1 frequency *
          complexVectorL1 (fun component ↦ (state component).1 parent)) *
        complexVectorL1
          (fun component ↦ (state component).1 (frequency - parent)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdot (norm_nonneg _)) htransported
    _ = _ := by ring

/-- The complete rotated interaction population is summable as a complex-vector current. -/
theorem summable_fixedOutputVelocityAdvectionTerms
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) :
    Summable fun parent : SpatialFrequency ↦
      (unitTorusCurlScale *
        complexDot (complexFrequencyVector frequency)
          (fun component ↦ (state component).1 parent)) •
        (fun component ↦ (state component).1 (frequency - parent)) := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hpairs := lp.summable_mul hholder
    (vectorCoefficientL1FourierL2 state)
    (reflectedVectorCoefficientL1FourierL2 state frequency)
  have hpairs' : Summable fun parent : SpatialFrequency ↦
      complexVectorL1 (fun component ↦ (state component).1 parent) *
        complexVectorL1
          (fun component ↦ (state component).1 (frequency - parent)) := by
    simpa only [vectorCoefficientL1FourierL2,
      reflectedVectorCoefficientL1FourierL2, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (complexVectorL1_nonneg _)] using hpairs
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun parent ↦ norm_nonneg _) (fun parent ↦ ?_)
    (hpairs'.mul_left (‖unitTorusCurlScale‖ * frequencyL1 frequency))
  exact (norm_complexVector_le_complexVectorL1 _).trans
    (complexVectorL1_fixedOutputVelocityAdvectionTerm_le state frequency parent)

/-- The complete fixed-output convolution is bounded by its coefficient Hilbert mass. -/
theorem complexVectorL1_fixedOutputVelocityAdvectionMode_le
    (state : PeriodicVectorSobolevThree) (frequency : SpatialFrequency) :
    complexVectorL1 (fixedOutputVelocityAdvectionMode state frequency) ≤
      ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        ‖vectorCoefficientL1FourierL2 state‖ ^ 2 := by
  let term : SpatialFrequency → ComplexVector := fun parent ↦
    (unitTorusCurlScale *
      complexDot (complexFrequencyVector frequency)
        (fun component ↦ (state component).1 parent)) •
      (fun component ↦ (state component).1 (frequency - parent))
  let pairMass : SpatialFrequency → ℝ := fun parent ↦
    complexVectorL1 (fun component ↦ (state component).1 parent) *
      complexVectorL1
        (fun component ↦ (state component).1 (frequency - parent))
  let scale : ℝ := ‖unitTorusCurlScale‖ * frequencyL1 frequency
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  have hpair : Summable pairMass := by
    have hnamed := lp.summable_mul hholder
      (vectorCoefficientL1FourierL2 state)
      (reflectedVectorCoefficientL1FourierL2 state frequency)
    simpa only [pairMass, vectorCoefficientL1FourierL2,
      reflectedVectorCoefficientL1FourierL2, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (complexVectorL1_nonneg _)] using hnamed
  have hscale : 0 ≤ scale :=
    mul_nonneg (norm_nonneg _) (frequencyL1_nonneg frequency)
  have hmajor : Summable fun parent ↦ scale * pairMass parent :=
    hpair.mul_left scale
  have htermBound (parent : SpatialFrequency) :
      complexVectorL1 (term parent) ≤ scale * pairMass parent := by
    simpa only [term, scale, pairMass, mul_assoc] using
      complexVectorL1_fixedOutputVelocityAdvectionTerm_le state frequency parent
  have hcoordinateNorm (component : Fin 3) :
      Summable fun parent ↦ ‖term parent component‖ := by
    refine Summable.of_nonneg_of_le (fun parent ↦ norm_nonneg _) (fun parent ↦ ?_) hmajor
    exact (Finset.single_le_sum
      (fun selected _hselected ↦ norm_nonneg (term parent selected))
      (Finset.mem_univ component)).trans
      (by simpa [complexVectorL1, Fin.sum_univ_succ, add_assoc] using htermBound parent)
  have htermNorm : Summable fun parent ↦ ‖term parent‖ := by
    refine Summable.of_nonneg_of_le (fun parent ↦ norm_nonneg _) (fun parent ↦ ?_) hmajor
    exact (norm_complexVector_le_complexVectorL1 (term parent)).trans (htermBound parent)
  have hterm : Summable term := Summable.of_norm htermNorm
  have hcoordinateTriangle (component : Fin 3) :
      ‖(∑' parent, term parent) component‖ ≤
        ∑' parent, ‖term parent component‖ := by
    let evaluation : ComplexVector →L[ℂ] ℂ :=
      ContinuousLinearMap.proj component
    change ‖evaluation (∑' parent, term parent)‖ ≤ _
    rw [evaluation.map_tsum hterm]
    exact norm_tsum_le_tsum_norm (hcoordinateNorm component)
  have hcoordinateTerms : ∀ component ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun parent ↦ ‖term parent component‖ := by
    intro component _hcomponent
    exact hcoordinateNorm component
  have hpairBound :=
    tsum_vectorCoefficientL1_mul_reflected_le_norm_sq state frequency
  have htermL1 : Summable fun parent ↦ complexVectorL1 (term parent) := by
    simpa [complexVectorL1, Fin.sum_univ_succ, add_assoc] using
      (hcoordinateNorm 0).add ((hcoordinateNorm 1).add (hcoordinateNorm 2))
  calc
    complexVectorL1 (fixedOutputVelocityAdvectionMode state frequency) =
        ∑ component : Fin 3, ‖(∑' parent, term parent) component‖ := by
      simp only [fixedOutputVelocityAdvectionMode, term]
      simp [complexVectorL1, Fin.sum_univ_succ, add_assoc]
    _ ≤ ∑ component : Fin 3, ∑' parent, ‖term parent component‖ :=
      Finset.sum_le_sum fun component _hcomponent ↦ hcoordinateTriangle component
    _ = ∑' parent, ∑ component : Fin 3, ‖term parent component‖ := by
      rw [Summable.tsum_finsetSum hcoordinateTerms]
    _ = ∑' parent, complexVectorL1 (term parent) := by
      apply tsum_congr
      intro parent
      simp [complexVectorL1, Fin.sum_univ_succ, add_assoc]
    _ ≤ ∑' parent, scale * pairMass parent :=
      Summable.tsum_le_tsum (fun parent ↦ htermBound parent) htermL1 hmajor
    _ = scale * ∑' parent, pairMass parent := hpair.tsum_mul_left scale
    _ ≤ scale * ‖vectorCoefficientL1FourierL2 state‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hpairBound hscale
    _ = ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        ‖vectorCoefficientL1FourierL2 state‖ ^ 2 := rfl

/-! ## Actual open-solution identification and kinetic payment -/

/-- The literal actual advection coefficient is the incompressibly rotated fixed-output
convolution.  This is the key derivative shift; no norm receiver has yet been taken. -/
theorem openActualAdvectionMode_eq_fixedOutputVelocityAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    openActualAdvectionMode solution t frequency =
      fixedOutputVelocityAdvectionMode
        (openVelocityH3State solution t) frequency := by
  rw [openActualAdvectionMode_eq_h3AdvectiveConvolution]
  unfold openVelocityH3State
  funext output
  change h3AdvectiveConvolution
      (smoothSliceH3State (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))
      (smoothSliceH3State (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) output frequency = _
  rw [h3AdvectiveConvolution_coefficient_eq_tsum_complexAdvectiveInteraction
    _ (periodicVectorSobolevThree_hasAbsolutelySummableComponents _) frequency output]
  let state := smoothSliceH3State (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
  have hrotated (parent : SpatialFrequency) :
      complexAdvectiveInteraction parent (frequency - parent)
          (fun component ↦ (state component).1 parent)
          (fun component ↦ (state component).1 (frequency - parent)) =
        (unitTorusCurlScale *
          complexDot (complexFrequencyVector frequency)
            (fun component ↦ (state component).1 parent)) •
          (fun component ↦ (state component).1 (frequency - parent)) := by
    apply complexAdvectiveInteraction_eq_fixedOutput_of_divergenceFree
    have hmode :
        (fun component ↦ (state component).1 parent) =
          openPeriodicVelocityFourierMode solution t parent := by
      funext component
      simpa only [state, openVelocityH3State] using
        openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
          solution t component parent
    rw [hmode]
    exact openPeriodicVelocityFourierMode_divergenceFree solution t parent
  change (∑' parent : SpatialFrequency,
      complexAdvectiveInteraction parent (frequency - parent)
        (fun component ↦ (state component).1 parent)
        (fun component ↦ (state component).1 (frequency - parent)) output) = _
  let rotated : SpatialFrequency → ComplexVector := fun parent ↦
    (unitTorusCurlScale *
      complexDot (complexFrequencyVector frequency)
        (fun component ↦ (state component).1 parent)) •
      (fun component ↦ (state component).1 (frequency - parent))
  have hrotatedSummable : Summable rotated := by
    simpa only [rotated] using
      summable_fixedOutputVelocityAdvectionTerms state frequency
  let evaluation : ComplexVector →L[ℂ] ℂ :=
    ContinuousLinearMap.proj output
  change (∑' parent : SpatialFrequency,
      complexAdvectiveInteraction parent (frequency - parent)
        (fun component ↦ (state component).1 parent)
        (fun component ↦ (state component).1 (frequency - parent)) output) =
    evaluation (∑' parent, rotated parent)
  rw [evaluation.map_tsum hrotatedSummable]
  exact tsum_congr fun parent ↦ congrFun (hrotated parent) output

/-- The complete componentwise cube energy is exactly twice kinetic energy. -/
theorem sum_componentCubeEnergy_eq_two_mul_periodicKineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    (∑ component : Fin 3,
        ∫ x in unitCube, (velocity x t.1 component) ^ 2) =
      2 * periodicKineticEnergy velocity t.1 := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hslice := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have hcomponentIntegrable (component : Fin 3) :
      IntegrableOn (fun x : Space ↦ (velocity x t.1 component) ^ 2) unitCube :=
    (((EuclideanSpace.proj component).continuous.comp hslice.continuous).pow 2).continuousOn
      |>.integrableOn_compact hcubeCompact
  calc
    (∑ component : Fin 3,
        ∫ x in unitCube, (velocity x t.1 component) ^ 2) =
      ∫ x in unitCube,
        ∑ component : Fin 3, (velocity x t.1 component) ^ 2 := by
      rw [integral_finsetSum Finset.univ]
      intro component _hcomponent
      exact hcomponentIntegrable component
    _ = ∫ x in unitCube, ‖velocity x t.1‖ ^ 2 := by
      apply setIntegral_congr_fun hcubeCompact.measurableSet
      intro x _hx
      exact (EuclideanSpace.real_norm_sq_eq (velocity x t.1)).symm
    _ = 2 * periodicKineticEnergy velocity t.1 := by
      unfold periodicKineticEnergy kineticEnergyDensity
      rw [← integral_const_mul]
      apply setIntegral_congr_fun hcubeCompact.measurableSet
      intro x _hx
      ring

/-- Parseval pays the complete vector-`L1` coefficient mass by six copies of kinetic energy.
The factor is `3` from the exact three-component Cauchy inequality and `2` from the kinetic
normalization. -/
theorem norm_vectorCoefficientL1FourierL2_openVelocityH3State_sq_le_kineticEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    ‖vectorCoefficientL1FourierL2 (openVelocityH3State solution t)‖ ^ 2 ≤
      6 * periodicKineticEnergy velocity t.1 := by
  let state : PeriodicVectorSobolevThree := openVelocityH3State solution t
  have hsource : Summable fun frequency : SpatialFrequency ↦
      complexVectorL1 (fun component ↦ (state component).1 frequency) ^ 2 := by
    have hnamed := (lp.memℓp (vectorCoefficientL1FourierL2 state)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      vectorCoefficientL1FourierL2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexVectorL1_nonneg _)] using hnamed
  have hcomponent (component : Fin 3) : Summable fun frequency : SpatialFrequency ↦
      ‖(state component).1 frequency‖ ^ 2 := by
    have hnamed := (lp.memℓp (state component).1).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hnamed
  have hcomponentTerms : ∀ component ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun frequency : SpatialFrequency ↦
        ‖(state component).1 frequency‖ ^ 2 := by
    intro component _hcomponent
    exact hcomponent component
  have htotal : Summable fun frequency : SpatialFrequency ↦
      ∑ component : Fin 3, ‖(state component).1 frequency‖ ^ 2 := by
    exact summable_sum fun component _hcomponent ↦ hcomponent component
  have hmass := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (vectorCoefficientL1FourierL2 state)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at hmass
  have hmass' :
      ‖vectorCoefficientL1FourierL2 state‖ ^ 2 =
        ∑' frequency : SpatialFrequency,
          complexVectorL1 (fun component ↦ (state component).1 frequency) ^ 2 := by
    simpa only [vectorCoefficientL1FourierL2, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (complexVectorL1_nonneg _)] using hmass
  have hpoint (frequency : SpatialFrequency) :
      complexVectorL1 (fun component ↦ (state component).1 frequency) ^ 2 ≤
        3 * ∑ component : Fin 3, ‖(state component).1 frequency‖ ^ 2 :=
    complexVectorL1_sq_le_three_mul_sum_norm_sq _
  have hweighted := htotal.mul_left 3
  calc
    ‖vectorCoefficientL1FourierL2 (openVelocityH3State solution t)‖ ^ 2 =
        ∑' frequency : SpatialFrequency,
          complexVectorL1 (fun component ↦ (state component).1 frequency) ^ 2 := by
      simpa only [state] using hmass'
    _ ≤ ∑' frequency : SpatialFrequency,
        3 * ∑ component : Fin 3, ‖(state component).1 frequency‖ ^ 2 :=
      Summable.tsum_le_tsum hpoint hsource hweighted
    _ = 3 * ∑' frequency : SpatialFrequency,
        ∑ component : Fin 3, ‖(state component).1 frequency‖ ^ 2 :=
      htotal.tsum_mul_left 3
    _ = 3 * ∑ component : Fin 3,
        ∑' frequency : SpatialFrequency,
          ‖(state component).1 frequency‖ ^ 2 := by
      rw [Summable.tsum_finsetSum hcomponentTerms]
    _ = 3 * ∑ component : Fin 3,
        ∫ x in unitCube, (velocity x t.1 component) ^ 2 := by
      apply congrArg (fun mass : ℝ ↦ 3 * mass)
      apply Finset.sum_congr rfl
      intro component _hcomponent
      unfold state openVelocityH3State smoothSliceH3State
      simpa only [smoothSliceSobolevCoefficients] using
        tsum_sq_smoothSliceFourierL2_eq_integral_unitCube
          (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component
    _ = 3 * (2 * periodicKineticEnergy velocity t.1) := by
      rw [sum_componentCubeEnergy_eq_two_mul_periodicKineticEnergy solution t]
    _ = 6 * periodicKineticEnergy velocity t.1 := by ring

/-! ## The projected physical source and finite low-output consequence -/

/-- The standing coordinatewise Leray estimate gives the explicit vector-`L1` constant six. -/
theorem complexVectorL1_lerayProjectMode_le_six
    (frequency : SpatialFrequency) (mode : ComplexVector) :
    complexVectorL1 (lerayProjectMode frequency mode) ≤
      6 * complexVectorL1 mode := by
  rw [show complexVectorL1 (lerayProjectMode frequency mode) =
      ∑ output : Fin 3, ‖lerayProjectMode frequency mode output‖ by
    simp [complexVectorL1, Fin.sum_univ_succ, add_assoc]]
  calc
    (∑ output : Fin 3, ‖lerayProjectMode frequency mode output‖) ≤
        ∑ _output : Fin 3, 2 * ∑ component : Fin 3, ‖mode component‖ :=
      Finset.sum_le_sum fun output _houtput ↦
        norm_lerayProjectMode_coordinate_le frequency mode output
    _ = 6 * complexVectorL1 mode := by
      simp [complexVectorL1, Fin.sum_univ_succ, add_assoc]
      ring

/-- At one fixed output, the actual signed projected velocity source is paid by the kinetic
energy of the same strict-interior slice. -/
theorem complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_kinetic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    complexVectorL1 (openProjectedVelocityNonlinearMode solution t frequency) ≤
      36 * ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        periodicKineticEnergy velocity t.1 := by
  have hfixed := complexVectorL1_fixedOutputVelocityAdvectionMode_le
    (openVelocityH3State solution t) frequency
  have hmass :=
    norm_vectorCoefficientL1FourierL2_openVelocityH3State_sq_le_kineticEnergy
      solution t
  have hscale : 0 ≤ ‖unitTorusCurlScale‖ * frequencyL1 frequency :=
    mul_nonneg (norm_nonneg _) (frequencyL1_nonneg frequency)
  calc
    complexVectorL1 (openProjectedVelocityNonlinearMode solution t frequency) =
        complexVectorL1
          (lerayProjectMode frequency (openActualAdvectionMode solution t frequency)) := by
      unfold openProjectedVelocityNonlinearMode
      simp [complexVectorL1]
    _ ≤ 6 * complexVectorL1 (openActualAdvectionMode solution t frequency) :=
      complexVectorL1_lerayProjectMode_le_six frequency _
    _ = 6 * complexVectorL1
        (fixedOutputVelocityAdvectionMode
          (openVelocityH3State solution t) frequency) := by
      rw [openActualAdvectionMode_eq_fixedOutputVelocityAdvectionMode]
    _ ≤ 6 * (‖unitTorusCurlScale‖ * frequencyL1 frequency *
        ‖vectorCoefficientL1FourierL2 (openVelocityH3State solution t)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hfixed (by norm_num)
    _ ≤ 6 * (‖unitTorusCurlScale‖ * frequencyL1 frequency *
        (6 * periodicKineticEnergy velocity t.1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass hscale) (by norm_num)
    _ = 36 * ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        periodicKineticEnergy velocity t.1 := by ring

/-- **Unconditional low-output payment from the admitted initial trace.**  Nonnegative viscosity
is the physical sign needed by the exact unforced energy law.  No output-tail sum is claimed. -/
theorem complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_initialKinetic
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (t : Ioo 0 T) (frequency : SpatialFrequency) :
    complexVectorL1 (openProjectedVelocityNonlinearMode solution t frequency) ≤
      36 * ‖unitTorusCurlScale‖ * frequencyL1 frequency *
        periodicKineticEnergy velocity 0 := by
  have hmode :=
    complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_kinetic
      solution t frequency
  have henergy := openPeriodicSolutionOn_periodicKineticEnergy_le_initial
    solution hnu t.2
  have hscale : 0 ≤ 36 * ‖unitTorusCurlScale‖ * frequencyL1 frequency := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _))
      (frequencyL1_nonneg frequency)
  exact hmode.trans (mul_le_mul_of_nonneg_left henergy hscale)

/-- A genuinely finite output selector inherits the low-output payment.  The selector keeps its
exact frequency population; this statement cannot be passed to an infinite high tail. -/
theorem sum_complexVectorL1_openProjectedVelocityNonlinearMode_le_finiteOutputFrequencyMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (t : Ioo 0 T) (outputs : Finset SpatialFrequency) :
    (∑ frequency ∈ outputs,
        complexVectorL1 (openProjectedVelocityNonlinearMode solution t frequency)) ≤
      (36 * ‖unitTorusCurlScale‖ * periodicKineticEnergy velocity 0) *
        ∑ frequency ∈ outputs, frequencyL1 frequency := by
  calc
    (∑ frequency ∈ outputs,
        complexVectorL1 (openProjectedVelocityNonlinearMode solution t frequency)) ≤
      ∑ frequency ∈ outputs,
        36 * ‖unitTorusCurlScale‖ * frequencyL1 frequency *
          periodicKineticEnergy velocity 0 := by
      exact Finset.sum_le_sum fun frequency _hfrequency ↦
        complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_initialKinetic
          solution hnu t frequency
    _ = (36 * ‖unitTorusCurlScale‖ * periodicKineticEnergy velocity 0) *
        ∑ frequency ∈ outputs, frequencyL1 frequency := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      ring

section Audit

#print axioms h3AdvectiveConvolution_coefficient_eq_tsum_complexAdvectiveInteraction
#print axioms complexAdvectiveInteraction_eq_fixedOutput_of_divergenceFree
#print axioms norm_reflectedVectorCoefficientL1FourierL2
#print axioms tsum_vectorCoefficientL1_mul_reflected_le_norm_sq
#print axioms complexVectorL1_fixedOutputVelocityAdvectionMode_le
#print axioms openActualAdvectionMode_eq_fixedOutputVelocityAdvectionMode
#print axioms norm_vectorCoefficientL1FourierL2_openVelocityH3State_sq_le_kineticEnergy
#print axioms complexVectorL1_lerayProjectMode_le_six
#print axioms complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_kinetic
#print axioms complexVectorL1_openProjectedVelocityNonlinearMode_le_outputFrequency_mul_initialKinetic
#print axioms sum_complexVectorL1_openProjectedVelocityNonlinearMode_le_finiteOutputFrequencyMass

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectedSourceLowOutputBound
