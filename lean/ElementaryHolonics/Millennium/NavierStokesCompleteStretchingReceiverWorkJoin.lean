import ElementaryHolonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverClosure

/-!
# Complete stretching contribution at the symmetric receiver-work chart

**[proved-derived; formal-checked]**  This owner completes the stretching leg which is separate
from transport exchange.  A complete stretching address retains the output and advecting
vorticity pins; the transported velocity pin is their returned difference.  Absolute
summability permits the pair-compatible parent aperture to pass to the complete fibre at each
of the finitely many output receivers.

Combining that limit with the completed transport receiver and the native finite nonlinear-work
limit identifies the actual fixed-depth `linearMultiplierCoefficientWork` as complete stretching
minus complete transport.  No scale/time passage or terminal estimate is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## One complete output fibre -/

/-- The complete symmetric stretching phase at one output frequency. -/
def completeReceiverStretchingPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) : ℂ :=
  ∑' parent : SpatialFrequency,
    completeOpenVorticityStretchingFace solution t (output, parent)

/-- Every fixed-output stretching fibre is absolutely summable. -/
theorem summable_norm_completeReceiverStretchingPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    Summable fun parent : SpatialFrequency ↦
      ‖completeOpenVorticityStretchingFace solution t (output, parent)‖ := by
  apply (summable_norm_completeOpenVorticityStretchingFace solution t).comp_injective
  intro first second heq
  exact congrArg Prod.snd heq

/-- Symmetric pairing is additive over a finite family in its right input. -/
theorem complexVectorSymmetricPhasePairing_finsetSum_right
    (left : ComplexVector) (population : SpatialFrequency → ComplexVector)
    (aperture : Finset SpatialFrequency) :
    complexVectorSymmetricPhasePairing left
        (∑ parent ∈ aperture, population parent) =
      ∑ parent ∈ aperture,
        complexVectorSymmetricPhasePairing left (population parent) := by
  classical
  induction aperture using Finset.induction_on with
  | empty =>
      simp [complexVectorSymmetricPhasePairing, complexVectorHermitianPairing]
  | @insert parent aperture hparent inductionHypothesis =>
      rw [Finset.sum_insert hparent, Finset.sum_insert hparent,
        complexVectorSymmetricPhasePairing_add_right_public,
        inductionHypothesis]

/-- The finite stretching coefficient work is exactly the finite sum of complete stretching
faces.  The Hermitian factor is already retained inside each face. -/
theorem complexVectorSymmetricPhasePairing_finiteStretchingCoefficient_eq_faceSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency)
    (aperture : Finset SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t output)
        (finiteAdvectiveCoefficient aperture
          (openPeriodicVorticityFourierMode solution t)
          (openPeriodicVelocityFourierMode solution t) output) =
      ∑ parent ∈ aperture,
        completeOpenVorticityStretchingFace solution t (output, parent) := by
  unfold finiteAdvectiveCoefficient
  rw [complexVectorSymmetricPhasePairing_finsetSum_right]
  apply Finset.sum_congr rfl
  intro parent _hparent
  exact (completeOpenVorticityStretchingFace_eq_pairing
    solution t (output, parent)).symm

/-- Pair-compatible finite stretching phases converge to the complete output fibre. -/
theorem tendsto_pairCompatibleReceiverStretchingPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t output)
          (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
            (openPeriodicVorticityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) output))
      atTop
      (nhds (completeReceiverStretchingPhaseAtOutput solution t output)) := by
  have hsum := tendsto_sum_pairCompatibleFrequencyAperture output
    (summable_norm_completeReceiverStretchingPhaseAtOutput
      solution t output).of_norm
  apply Tendsto.congr' _ hsum
  exact Filter.Eventually.of_forall fun radius ↦
    (complexVectorSymmetricPhasePairing_finiteStretchingCoefficient_eq_faceSum
      solution t output (pairCompatibleFrequencyAperture output radius)).symm

/-! ## Finite output receiver and its actual nonlinear-work join -/

/-- The complete stretching work retained by the finite native output receiver. -/
def completeReceiverStretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑ output ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth output : ℂ) *
      completeReceiverStretchingPhaseAtOutput solution t output

/-- The finite pair-compatible stretching receiver work converges to its complete parent
population while preserving the finite output aperture. -/
theorem tendsto_finitePairCompatibleReceiverStretchingWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleReceiverStretchingWork solution t depth radius)
      atTop
      (nhds (completeReceiverStretchingWork solution t depth)) := by
  unfold finitePairCompatibleReceiverStretchingWork
    completeReceiverStretchingWork
  apply tendsto_finsetSum
  intro output _houtput
  exact tendsto_const_nhds.mul
    (tendsto_pairCompatibleReceiverStretchingPhase solution t output)

/-! ## Transported-velocity multiplier chart and output reconstruction fibre -/

/-- Applying the real strain multiplier to the transported velocity pin weights each complete
stretching face by that pin's frequency. -/
theorem complexVectorSymmetricPhasePairing_weightedStretchingInteraction_eq_face
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) (output parent : SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t output)
        (complexAdvectiveInteraction parent (output - parent)
          (openPeriodicVorticityFourierMode solution t parent)
          (multiplierFilter
            (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
            (openPeriodicVelocityFourierMode solution t) (output - parent))) =
      (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
        completeOpenVorticityStretchingFace solution t (output, parent) := by
  have hinteraction :
      complexAdvectiveInteraction parent (output - parent)
          (openPeriodicVorticityFourierMode solution t parent)
          (multiplierFilter
            (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
            (openPeriodicVelocityFourierMode solution t) (output - parent)) =
        (finiteDepthBoundaryWeight depth (output - parent) : ℂ) •
          complexAdvectiveInteraction parent (output - parent)
            (openPeriodicVorticityFourierMode solution t parent)
            (openPeriodicVelocityFourierMode solution t (output - parent)) := by
    funext component
    simp only [multiplierFilter, complexAdvectiveInteraction, Pi.smul_apply,
      smul_eq_mul]
    ring
  rw [hinteraction, complexVectorSymmetricPhasePairing_real_smul_right,
    completeOpenVorticityStretchingFace_eq_pairing]

/-- The finite strain-filtered phase is the finite weighted stretching-face sum. -/
theorem complexVectorSymmetricPhasePairing_finiteStrainFilteredCoefficient_eq_faceSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) (output : SpatialFrequency)
    (aperture : Finset SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t output)
        (finiteAdvectiveCoefficient aperture
          (openPeriodicVorticityFourierMode solution t)
          (multiplierFilter
            (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
            (openPeriodicVelocityFourierMode solution t)) output) =
      ∑ parent ∈ aperture,
        (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
          completeOpenVorticityStretchingFace solution t (output, parent) := by
  unfold finiteAdvectiveCoefficient
  rw [complexVectorSymmetricPhasePairing_finsetSum_right]
  apply Finset.sum_congr rfl
  intro parent _hparent
  exact complexVectorSymmetricPhasePairing_weightedStretchingInteraction_eq_face
    solution t depth output parent

/-- The complete strain-filtered stretching fibre at one retained output. -/
def completeStrainFilteredStretchingPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) : ℂ :=
  ∑' parent : SpatialFrequency,
    (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
      completeOpenVorticityStretchingFace solution t (output, parent)

theorem summable_completeStrainFilteredStretchingPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) :
    Summable fun parent : SpatialFrequency ↦
      (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
        completeOpenVorticityStretchingFace solution t (output, parent) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun parent ↦ ?_)
    (summable_norm_completeReceiverStretchingPhaseAtOutput solution t output)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (abs_finiteDepthBoundaryWeight_le_one depth (output - parent))

/-- The interaction-radius passage for the strain-filtered chart retains the finite output
receiver exactly. -/
theorem tendsto_pairCompatibleStrainFilteredStretchingPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) :
    Tendsto
      (fun radius : ℕ ↦
        complexVectorSymmetricPhasePairing
          (openPeriodicVorticityFourierMode solution t output)
          (finiteAdvectiveCoefficient (pairCompatibleFrequencyAperture output radius)
            (openPeriodicVorticityFourierMode solution t)
            (multiplierFilter
              (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
              (openPeriodicVelocityFourierMode solution t)) output))
      atTop
      (nhds (completeStrainFilteredStretchingPhaseAtOutput
        solution t depth output)) := by
  have hsum := tendsto_sum_pairCompatibleFrequencyAperture output
    (summable_completeStrainFilteredStretchingPhaseAtOutput
      solution t depth output)
  apply Tendsto.congr' _ hsum
  exact Filter.Eventually.of_forall fun radius ↦
    (complexVectorSymmetricPhasePairing_finiteStrainFilteredCoefficient_eq_faceSum
      solution t depth output
        (pairCompatibleFrequencyAperture output radius)).symm

/-- The interaction-complete strain-filtered work with its original finite output aperture. -/
def completeOutputCompatibleStrainFilteredStretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑ output ∈ smoothDyadicBandNativeAperture depth,
    completeStrainFilteredStretchingPhaseAtOutput solution t depth output

/-- **Finite output-compatible stretching limit.**  Only the interaction parent aperture is
removed; the native output receiver remains explicit. -/
theorem tendsto_finitePairCompatibleStrainFilteredStretchingWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleStrainFilteredStretchingWork solution t depth radius)
      atTop
      (nhds (completeOutputCompatibleStrainFilteredStretchingWork
        solution t depth)) := by
  unfold finitePairCompatibleStrainFilteredStretchingWork
    completeOutputCompatibleStrainFilteredStretchingWork
  apply tendsto_finsetSum
  intro output _houtput
  exact tendsto_pairCompatibleStrainFilteredStretchingPhase
    solution t depth output

/-! ## Complete output reconstruction fibre -/

/-- The strain-filtered stretching work before truncating the output population. -/
def completeStrainFilteredStretchingWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      completeOpenVorticityStretchingFace solution t address

theorem summable_completeStrainFilteredStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Summable fun address : CompleteStretchingAddress ↦
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        completeOpenVorticityStretchingFace solution t address := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_norm_completeOpenVorticityStretchingFace solution t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))

/-- The finite output-compatible complete work is the total of the complete population selected
by the native output aperture. -/
theorem completeOutputCompatibleStrainFilteredStretchingWork_eq_tsum_restricted
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeOutputCompatibleStrainFilteredStretchingWork solution t depth =
      ∑' address : CompleteStretchingAddress,
        if address.1 ∈ smoothDyadicBandNativeAperture depth then
          (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
            completeOpenVorticityStretchingFace solution t address
        else 0 := by
  let restricted : CompleteStretchingAddress → ℂ := fun address ↦
    if address.1 ∈ smoothDyadicBandNativeAperture depth then
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        completeOpenVorticityStretchingFace solution t address
    else 0
  have hrestricted : Summable restricted := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
      (summable_norm_completeOpenVorticityStretchingFace solution t)
    unfold restricted
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))
    · simp
  have hfiber (output : SpatialFrequency) : Summable fun parent ↦
      restricted (output, parent) := by
    apply hrestricted.comp_injective
    intro first second heq
    exact congrArg Prod.snd heq
  have hprod := hrestricted.tsum_prod' hfiber
  rw [hprod]
  rw [tsum_eq_sum (s := smoothDyadicBandNativeAperture depth)
    (fun output houtput ↦ by simp [restricted, houtput])]
  unfold completeOutputCompatibleStrainFilteredStretchingWork
    completeStrainFilteredStretchingPhaseAtOutput
  apply Finset.sum_congr rfl
  intro output houtput
  apply tsum_congr
  intro parent
  simp [restricted, houtput]

/-- Exact reconstruction: the full strain-filtered stretching population is the retained finite
output receiver plus the complete omitted-output fibre exposed by the cofinal closure owner. -/
theorem completeStrainFilteredStretchingWork_eq_outputCompatible_add_highOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeStrainFilteredStretchingWork solution t depth =
      completeOutputCompatibleStrainFilteredStretchingWork solution t depth +
        cofinalStrainHighOutputPopulation solution t depth := by
  let restricted : CompleteStretchingAddress → ℂ := fun address ↦
    if address.1 ∈ smoothDyadicBandNativeAperture depth then
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        completeOpenVorticityStretchingFace solution t address
    else 0
  have hrestricted : Summable restricted := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
      (summable_norm_completeOpenVorticityStretchingFace solution t)
    unfold restricted
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))
    · simp
  have hhigh := summable_cofinalStrainHighOutputFace solution t depth
  rw [completeOutputCompatibleStrainFilteredStretchingWork_eq_tsum_restricted]
  change (∑' address : CompleteStretchingAddress,
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        completeOpenVorticityStretchingFace solution t address) =
    (∑' address : CompleteStretchingAddress, restricted address) +
      ∑' address : CompleteStretchingAddress,
        cofinalStrainHighOutputFace solution t depth address
  rw [← hrestricted.tsum_add hhigh]
  apply tsum_congr
  intro address
  by_cases houtput : address.1 ∈ smoothDyadicBandNativeAperture depth
  · simp [restricted, cofinalStrainHighOutputFace, houtput]
  · simp [restricted, cofinalStrainHighOutputFace, houtput]

/-- The complete high-output reconstruction fibre vanishes cofinally in depth; this is an
integrated output-population statement, not pointwise spatial receiver closure. -/
theorem tendsto_completeStrainFiltered_sub_outputCompatible_zero
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto
      (fun depth : ℕ ↦
        completeStrainFilteredStretchingWork solution t depth -
          completeOutputCompatibleStrainFilteredStretchingWork solution t depth)
      atTop (nhds 0) := by
  apply Tendsto.congr' _
    (tendsto_cofinalStrainHighOutputPopulation_zero solution t)
  exact Filter.Eventually.of_forall fun depth ↦ by
    change cofinalStrainHighOutputPopulation solution t depth =
      completeStrainFilteredStretchingWork solution t depth -
        completeOutputCompatibleStrainFilteredStretchingWork solution t depth
    rw [completeStrainFilteredStretchingWork_eq_outputCompatible_add_highOutput]
    ring

/-- **Actual fixed-depth nonlinear-work join.**  The native linear multiplier work against the
actual vorticity source is complete stretching receiver work minus complete transport receiver
work.  Both sides retain the same finite output population and Hermitian phase convention. -/
theorem linearMultiplierCoefficientWork_eq_completeStretching_sub_transport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t) =
      completeReceiverStretchingWork solution t depth -
        completeSymmetricReceiverTransportWork solution t depth := by
  have hactual :=
    tendsto_finitePairCompatibleBoundaryNonlinearWork solution t depth
  have htransport : Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleReceiverTransportWork solution t depth radius)
      atTop
      (nhds (completeSymmetricReceiverTransportWork solution t depth)) := by
    simpa only [completeSymmetricReceiverTransportWork_eq_neg_cumulative_symmetrization]
      using tendsto_finitePairCompatibleReceiverTransportWork_atTop
        solution t depth
  have hcomplete :=
    (tendsto_finitePairCompatibleReceiverStretchingWork_atTop
      solution t depth).sub htransport
  have hcomplete' : Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleBoundaryNonlinearWork solution t depth radius)
      atTop
      (nhds (completeReceiverStretchingWork solution t depth -
        completeSymmetricReceiverTransportWork solution t depth)) := by
    apply Tendsto.congr' _ hcomplete
    exact Filter.Eventually.of_forall fun radius ↦
      (finitePairCompatibleBoundaryNonlinearWork_eq_stretching_sub_transport
        solution t depth radius).symm
  exact tendsto_nhds_unique hactual hcomplete'

/-- Substituting the exact completed transport chart exposes the cumulative transport face with
its correct positive sign in the actual nonlinear work. -/
theorem linearMultiplierCoefficientWork_eq_completeStretching_add_cumulative_symmetrization
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    linearMultiplierCoefficientWork
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution t)
        (vorticityNonlinearMode solution t) =
      completeReceiverStretchingWork solution t depth +
        (1 / 2 : ℂ) *
          (completeCumulativeTransportContribution solution t depth +
            conj (completeCumulativeTransportContribution solution t depth)) := by
  rw [linearMultiplierCoefficientWork_eq_completeStretching_sub_transport,
    completeSymmetricReceiverTransportWork_eq_neg_cumulative_symmetrization]
  ring

section Audit

#print axioms tendsto_finitePairCompatibleReceiverStretchingWork_atTop
#print axioms tendsto_finitePairCompatibleStrainFilteredStretchingWork_atTop
#print axioms completeStrainFilteredStretchingWork_eq_outputCompatible_add_highOutput
#print axioms tendsto_completeStrainFiltered_sub_outputCompatible_zero
#print axioms linearMultiplierCoefficientWork_eq_completeStretching_sub_transport

end Audit

end Soma.Holonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
