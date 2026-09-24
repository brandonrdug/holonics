import ElementaryHolonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Cofinal output-receiver closure for the finite linear strain passage

**[proved-derived; formal-checked]**  Removing the interaction-radius aperture does not erase the
distinct output-frequency aperture.  This owner exposes the complete `(output,parent)` stretching
population selected by the cumulative Hodge multiplier.  Smooth coefficient summability gives a
single depth-independent summable majorant, so the population whose output lies outside the native
depth aperture converges to zero.

The physical/Fourier identification is kept as an exact spatial-integral obligation below.  The
present source owners do not yet identify the integral of the full-vorticity Hodge reading with
the complete output sum.  Consequently no pointwise receiver closure, terminal estimate, or
Navier--Stokes solution claim is made.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## Complete smooth stretching population -/

/-- One complete stretching address retains the output and advecting-vorticity pins.  The
transported velocity pin is their returned difference. -/
abbrev CompleteStretchingAddress := SpatialFrequency × SpatialFrequency

/-- The smooth `H³` coefficient carrier of one spatial derivative of the actual velocity slice. -/
def openVelocityDirectionalDerivativeH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate : Fin 3) : PeriodicVectorSobolevThree :=
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu : ContDiff ℝ (⊤ : ℕ∞) u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  smoothSliceH3State (spatialDirectionalJet u coordinate)
    (spatialDirectionalJet_contDiff u hu coordinate)
    (spatialDirectionalJet_isOnePeriodic u hperiodic coordinate)

theorem openVelocityDirectionalDerivativeH3State_apply_eq_derivative
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3) (frequency : SpatialFrequency) :
    (openVelocityDirectionalDerivativeH3State
      solution t coordinate output).1 frequency =
      periodicSobolevThreeDerivative coordinate
        (openVelocityH3State solution t output) frequency := by
  change smoothSliceFourierL2
      (spatialDirectionalJet (fun x ↦ velocity x t.1) coordinate)
      _ _ output frequency =
    periodicSobolevThreeDerivative coordinate
      (smoothSliceSobolevCoefficients (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) output) frequency
  rw [smoothSliceFourierL2_spatialDirectionalJet]
  rfl

/-- Every differentiated-velocity component is absolutely summable on an interior slice. -/
theorem summable_norm_openVelocityDirectionalDerivativeH3State_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      ‖(openVelocityDirectionalDerivativeH3State
        solution t coordinate output).1 frequency‖ :=
  periodicVectorSobolevThree_hasAbsolutelySummableComponents
    (openVelocityDirectionalDerivativeH3State solution t coordinate) output

/-- One coordinate-resolved first Hermitian stretching phase. -/
def completeOpenVorticityStretchingCoordinateFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3)
    (address : CompleteStretchingAddress) : ℂ :=
  (starRingEnd ℂ)
      (openPeriodicVorticityFourierMode solution t address.1 output) *
    openPeriodicVorticityFourierMode solution t address.2 coordinate *
    (openVelocityDirectionalDerivativeH3State
      solution t coordinate output).1 (address.1 - address.2)

/-- The complete unweighted symmetric stretching face at one `(output,parent)` address. -/
def completeOpenVorticityStretchingFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteStretchingAddress) : ℂ :=
  (1 / 2 : ℂ) *
    ((∑ output : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address) +
      conj (∑ output : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address))

/-- The coordinate face is exactly the first Hermitian phase of one complete stretching
interaction.  The derivative multiplier is inherited from the native smooth coefficient state. -/
theorem sum_completeOpenVorticityStretchingCoordinateFace_eq_hermitian
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteStretchingAddress) :
    (∑ output : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address) =
      complexVectorHermitianPairing
        (openPeriodicVorticityFourierMode solution t address.1)
        (complexAdvectiveInteraction address.2 (address.1 - address.2)
          (openPeriodicVorticityFourierMode solution t address.2)
          (openPeriodicVelocityFourierMode solution t (address.1 - address.2))) := by
  unfold complexVectorHermitianPairing completeOpenVorticityStretchingCoordinateFace
    complexAdvectiveInteraction complexDot dotProduct
  apply Finset.sum_congr rfl
  intro output _houtput
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [openVelocityDirectionalDerivativeH3State_apply_eq_derivative]
  rw [periodicSobolevThreeDerivative_apply]
  rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
  simp only [complexFrequencyVector]
  ring

/-- The complete face is the symmetric receiver applied to the literal one-parent stretching
interaction. -/
theorem completeOpenVorticityStretchingFace_eq_pairing
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteStretchingAddress) :
    completeOpenVorticityStretchingFace solution t address =
      complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t address.1)
        (complexAdvectiveInteraction address.2 (address.1 - address.2)
          (openPeriodicVorticityFourierMode solution t address.2)
          (openPeriodicVelocityFourierMode solution t (address.1 - address.2))) := by
  rw [completeOpenVorticityStretchingFace,
    sum_completeOpenVorticityStretchingCoordinateFace_eq_hermitian]
  unfold complexVectorSymmetricPhasePairing
  congr 2
  unfold complexVectorHermitianPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro output _houtput
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- One coefficient is bounded by the complete actual vorticity coefficient mass. -/
theorem norm_openPeriodicVorticityFourierMode_component_le_fullMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) (component : Fin 3) :
    ‖openPeriodicVorticityFourierMode solution t frequency component‖ ≤
      ∑' mode : SpatialFrequency,
        complexVectorL1 (openPeriodicVorticityFourierMode solution t mode) := by
  have hcomponent :
      ‖openPeriodicVorticityFourierMode solution t frequency component‖ ≤
        complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency) := by
    exact (norm_le_pi_norm
      (openPeriodicVorticityFourierMode solution t frequency) component).trans
        (norm_complexVector_le_complexVectorL1 _)
  have hsingle :=
    (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t).sum_le_tsum
      {frequency} (fun mode _hmode ↦ complexVectorL1_nonneg _)
  exact hcomponent.trans (by simpa using hsingle)

/-- Each coordinate-resolved complete stretching population is absolutely summable. -/
theorem summable_norm_completeOpenVorticityStretchingCoordinateFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate output : Fin 3) :
    Summable fun address : CompleteStretchingAddress ↦
      ‖completeOpenVorticityStretchingCoordinateFace
        solution t coordinate output address‖ := by
  let mass : ℝ := ∑' mode : SpatialFrequency,
    complexVectorL1 (openPeriodicVorticityFourierMode solution t mode)
  have hvorticity : Summable fun frequency : SpatialFrequency ↦
      ‖openPeriodicVorticityFourierMode solution t frequency coordinate‖ := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun frequency ↦ ?_)
      (summable_complexVectorL1_openPeriodicVorticityFourierMode solution t)
    exact (norm_le_pi_norm
      (openPeriodicVorticityFourierMode solution t frequency) coordinate).trans
        (norm_complexVector_le_complexVectorL1 _)
  have hderivative :=
    summable_norm_openVelocityDirectionalDerivativeH3State_component
      solution t coordinate output
  have hproduct : Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      ‖openPeriodicVorticityFourierMode solution t pair.1 coordinate‖ *
        ‖(openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 pair.2‖ :=
    hvorticity.mul_of_nonneg hderivative (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  let rebase : (SpatialFrequency × SpatialFrequency) ≃
      CompleteStretchingAddress :=
    { toFun := fun pair ↦ (pair.1 + pair.2, pair.1)
      invFun := fun address ↦ (address.2, address.1 - address.2)
      left_inv := by intro pair; ext <;> simp
      right_inv := by intro address; ext <;> simp }
  have hrebase : Summable fun address : CompleteStretchingAddress ↦
      ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
        ‖(openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 (address.1 - address.2)‖ := by
    exact (hproduct.comp_injective rebase.symm.injective).congr (fun address ↦ by
      change
        ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
            ‖(openVelocityDirectionalDerivativeH3State
              solution t coordinate output).1 (address.1 - address.2)‖ =
          ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
            ‖(openVelocityDirectionalDerivativeH3State
              solution t coordinate output).1 (address.1 - address.2)‖
      rfl)
  have hmajorant := hrebase.mul_right mass
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_) hmajorant
  rw [completeOpenVorticityStretchingCoordinateFace, norm_mul, norm_mul,
    starRingEnd_apply, norm_star]
  calc
    ‖openPeriodicVorticityFourierMode solution t address.1 output‖ *
          ‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
        ‖(openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 (address.1 - address.2)‖ =
      (‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
        ‖(openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 (address.1 - address.2)‖) *
          ‖openPeriodicVorticityFourierMode solution t address.1 output‖ := by ring
    _ ≤ (‖openPeriodicVorticityFourierMode solution t address.2 coordinate‖ *
        ‖(openVelocityDirectionalDerivativeH3State
          solution t coordinate output).1 (address.1 - address.2)‖) * mass := by
      exact mul_le_mul_of_nonneg_left
        (norm_openPeriodicVorticityFourierMode_component_le_fullMass
          solution t address.1 output)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- The complete symmetric stretching-face population is absolutely summable. -/
theorem summable_norm_completeOpenVorticityStretchingFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Summable fun address : CompleteStretchingAddress ↦
      ‖completeOpenVorticityStretchingFace solution t address‖ := by
  have hcoordinates : Summable fun address : CompleteStretchingAddress ↦
      ∑ output : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address‖ := by
    apply summable_sum
    intro output _houtput
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_norm_completeOpenVorticityStretchingCoordinateFace
      solution t coordinate output
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    hcoordinates
  unfold completeOpenVorticityStretchingFace
  let first := ∑ output : Fin 3, ∑ coordinate : Fin 3,
    completeOpenVorticityStretchingCoordinateFace
      solution t coordinate output address
  calc
    ‖(1 / 2 : ℂ) * (first + conj first)‖ ≤
        (1 / 2 : ℝ) * (‖first‖ + ‖conj first‖) := by
      rw [norm_mul]
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      exact mul_le_mul_of_nonneg_left (norm_add_le first (conj first)) (by norm_num)
    _ = ‖first‖ := by rw [starRingEnd_apply, norm_star]; ring
    _ ≤ ∑ output : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityStretchingCoordinateFace
          solution t coordinate output address‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun output _houtput ↦ norm_sum_le _ _)

/-! ## The actual high-output population and its cofinal vanishing -/

/-- The complete cumulative stretching face omitted by the finite native output aperture. -/
def cofinalStrainHighOutputFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (address : CompleteStretchingAddress) : ℂ :=
  if address.1 ∈ smoothDyadicBandNativeAperture depth then 0 else
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      completeOpenVorticityStretchingFace solution t address

/-- The signed high-output stretching tail after the interaction population is complete. -/
def cofinalStrainHighOutputPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    cofinalStrainHighOutputFace solution t depth address

theorem summable_cofinalStrainHighOutputFace
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    Summable (cofinalStrainHighOutputFace solution t depth) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_norm_completeOpenVorticityStretchingFace solution t)
  unfold cofinalStrainHighOutputFace
  split_ifs
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))

/-- Every fixed output frequency eventually belongs to the native depth aperture. -/
theorem eventually_mem_smoothDyadicBandNativeAperture
    (frequency : SpatialFrequency) :
    ∀ᶠ depth in atTop, frequency ∈ smoothDyadicBandNativeAperture depth := by
  obtain ⟨radius, hfrequency⟩ := exists_mem_frequencyCube frequency
  have hgrowth : Tendsto dyadicRadius atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2)
  filter_upwards [hgrowth.eventually (eventually_ge_atTop (radius + 1))] with depth hdepth
  unfold smoothDyadicBandNativeAperture
  have hcutoff : radius ≤ dyadicHodgeOuterCutoff (depth + 1) := by
    rw [dyadicHodgeOuterCutoff_eq]
    have hmono : dyadicRadius depth ≤ dyadicRadius (depth + 1 + 1) := by
      unfold dyadicRadius
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact frequencyCube_mono hcutoff hfrequency

/-- **Actual fixed-time receiver-tail closure.**  Smooth weighted-`H³` coefficient control
dominates the literal complete stretching population independently of depth, while every fixed
output address eventually enters the native aperture. -/
theorem tendsto_cofinalStrainHighOutputPopulation_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    Tendsto (cofinalStrainHighOutputPopulation solution t) atTop (nhds 0) := by
  have hpointwise (address : CompleteStretchingAddress) :
      Tendsto (fun depth ↦ cofinalStrainHighOutputFace solution t depth address)
        atTop (nhds 0) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_mem_smoothDyadicBandNativeAperture address.1]
      with depth hdepth
    simp [cofinalStrainHighOutputFace, hdepth]
  have hbound : ∀ᶠ depth in atTop, ∀ address : CompleteStretchingAddress,
      ‖cofinalStrainHighOutputFace solution t depth address‖ ≤
        ‖completeOpenVorticityStretchingFace solution t address‖ := by
    filter_upwards [] with depth address
    unfold cofinalStrainHighOutputFace
    split_ifs
    · simp
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))
  have htannery := tendsto_tsum_of_dominated_convergence
    (summable_norm_completeOpenVorticityStretchingFace solution t)
    hpointwise hbound
  change Tendsto
    (fun depth ↦ ∑' address : CompleteStretchingAddress,
      cofinalStrainHighOutputFace solution t depth address) atTop (nhds 0)
  simpa using htannery

/-! ## Exact receiver-integral obligation and the strongest current consequence -/

/-- The exact missing Fourier/physical join at the spatial receiver.  It equates only the torus
integral of the exposed cofinal defect with the literal high-output stretching population; it is
strictly weaker than pointwise `CompactFiniteDepthOutputReceiverClosure`. -/
def SpatialIntegratedCofinalOutputReceiverJoin
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) : Prop :=
  ∀ depth : ℕ,
    (∫ q : SpatialTorus,
      finiteDepthCofinalOutputReceiverDefect solution t depth q) =
        cofinalStrainHighOutputPopulation solution t depth

/-- Once the exact spatial Parseval/reconstruction join is supplied by its source owner, the
actual spatial integral of the cofinal output-receiver defect tends to zero. -/
theorem tendsto_integral_finiteDepthCofinalOutputReceiverDefect_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T)
    (hjoin : SpatialIntegratedCofinalOutputReceiverJoin solution t) :
    Tendsto (fun depth : ℕ ↦ ∫ q : SpatialTorus,
      finiteDepthCofinalOutputReceiverDefect solution t depth q)
      atTop (nhds 0) := by
  apply Tendsto.congr' _
    (tendsto_cofinalStrainHighOutputPopulation_zero solution t)
  exact Filter.Eventually.of_forall fun depth ↦ (hjoin depth).symm

section Audit

#print axioms summable_norm_completeOpenVorticityStretchingFace
#print axioms tendsto_cofinalStrainHighOutputPopulation_zero
#print axioms tendsto_integral_finiteDepthCofinalOutputReceiverDefect_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
