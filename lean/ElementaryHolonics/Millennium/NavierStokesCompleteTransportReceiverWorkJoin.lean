import ElementaryHolonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
import ElementaryHolonics.Millennium.NavierStokesWeightedReality

/-!
# Complete transport contribution at the symmetric receiver work chart

**[proved-derived; formal-checked]**  The complete ordered transport face is bilinear and keeps
the receiving mode at the closing frequency.  The linear-work owner instead uses the symmetric
Hermitian receiver at the output frequency.  This file preserves that distinction: Fourier
reality identifies the first Hermitian phase with the closing-face population, while the second
phase remains its complex conjugate.

The cofinal pair-compatible receiver work is therefore the negative Hermitian symmetrization of
the complete cumulative transport contribution.  The minus sign is the exact transported/
receiving exchange sign.  No finite output aperture is assumed exchange-closed.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFejerMultiplier
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPairCompatibleApertureConvergence
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTranslationDissipation
open Soma.Holonics.Millennium.NavierStokesWeightedReality

/-! ## Reality and even multiplier incidences -/

/-- The actual vorticity coefficient has the exact real-field Fourier incidence. -/
theorem openPeriodicVorticityFourierMode_neg_eq_conj
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (frequency : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution t (-frequency) =
      fun component ↦ conj
        (openPeriodicVorticityFourierMode solution t frequency component) := by
  funext component
  rw [← openPeriodicVorticityComponentFourierL2_apply,
    ← openPeriodicVorticityComponentFourierL2_apply]
  unfold openPeriodicVorticityComponentFourierL2
  rw [smoothSliceFourierL2_apply, smoothSliceFourierL2_apply]
  exact vectorSpatialFourierCoeff_neg_eq_conj
    (fun x ↦ vorticityField velocity x t.1)
    (openPeriodicSolutionOn_vorticitySlice_contDiff solution t).continuous
    (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
    frequency component

/-- Tensor de la Vallée Poussin weights are even on the integer character lattice. -/
theorem tensorValleePoussinWeight_neg
    (radius : ℕ) (frequency : SpatialFrequency) :
    tensorValleePoussinWeight radius (-frequency) =
      tensorValleePoussinWeight radius frequency := by
  unfold tensorValleePoussinWeight coordinateValleePoussinWeight coordinateHatWeight
  apply Finset.prod_congr rfl
  intro coordinate _hcoordinate
  simp only [Pi.neg_apply, Int.natAbs_neg]

theorem finiteDepthBoundaryWeight_neg
    (depth : ℕ) (frequency : SpatialFrequency) :
    finiteDepthBoundaryWeight depth (-frequency) =
      finiteDepthBoundaryWeight depth frequency := by
  unfold finiteDepthBoundaryWeight
  rw [tensorValleePoussinWeight_neg, tensorValleePoussinWeight_neg]

/-! ## One output fibre before symmetric phase collapse -/

/-- The complete first Hermitian phase at output `k`; its closed receiving pin is `-k`. -/
def completeReceiverTransportFirstPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) : ℂ :=
  ∑' parent : SpatialFrequency,
    completeOpenVorticityTransportFace solution t
      (parent, output - parent)

/-- Every fixed-output face fibre is absolutely summable as an injective slice of the complete
two-pin population. -/
theorem summable_norm_completeReceiverTransportFirstPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency) :
    Summable fun parent : SpatialFrequency ↦
      ‖completeOpenVorticityTransportFace solution t
        (parent, output - parent)‖ := by
  have hinjective : Function.Injective
      (fun parent : SpatialFrequency ↦ (parent, output - parent)) := by
    intro first second hequal
    exact congrArg Prod.fst hequal
  exact (summable_norm_completeOpenVorticityTransportFace solution t).comp_injective
    hinjective

/-- The first Hermitian phase of a finite transport coefficient is exactly the finite closed-face
sum.  Reality supplies the receiving coefficient at `-output`; no exchange closure is used. -/
theorem complexVectorHermitianPairing_finiteAdvectiveCoefficient_eq_faceSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency)
    (aperture : Finset SpatialFrequency) :
    complexVectorHermitianPairing
        (openPeriodicVorticityFourierMode solution t output)
        (finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (openPeriodicVorticityFourierMode solution t) output) =
      ∑ parent ∈ aperture,
        completeOpenVorticityTransportFace solution t
          (parent, output - parent) := by
  classical
  unfold complexVectorHermitianPairing finiteAdvectiveCoefficient
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro parent _hparent
  unfold completeOpenVorticityTransportFace triadicEnergyFace complexDot
  rw [show completeTransportReceiver (parent, output - parent) = -output by
    funext coordinate
    simp [completeTransportReceiver]
    ring]
  rw [openPeriodicVorticityFourierMode_neg_eq_conj solution t output]
  simp only [transportedFrequencyAt]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only
  ring

/-- Hermitian reversal is exact complex conjugation. -/
theorem complexVectorHermitianPairing_swap
    (left right : ComplexVector) :
    complexVectorHermitianPairing right left =
      conj (complexVectorHermitianPairing left right) := by
  unfold complexVectorHermitianPairing
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  simp only [map_mul, starRingEnd_self_apply]
  ring

/-- Thus the complete symmetric receiver phase is the literal Hermitian symmetrization of the
first closed-face fibre. -/
theorem complexVectorSymmetricPhasePairing_finiteAdvectiveCoefficient_eq_faceSum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (output : SpatialFrequency)
    (aperture : Finset SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t output)
        (finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (openPeriodicVorticityFourierMode solution t) output) =
      (1 / 2 : ℂ) *
        ((∑ parent ∈ aperture,
            completeOpenVorticityTransportFace solution t
              (parent, output - parent)) +
          conj (∑ parent ∈ aperture,
            completeOpenVorticityTransportFace solution t
              (parent, output - parent))) := by
  unfold complexVectorSymmetricPhasePairing
  rw [complexVectorHermitianPairing_finiteAdvectiveCoefficient_eq_faceSum]
  rw [complexVectorHermitianPairing_swap]
  rw [complexVectorHermitianPairing_finiteAdvectiveCoefficient_eq_faceSum]

/-! ## Cofinal receiver-work limit -/

/-- Each finite receiver phase converges to the complete closed-face fibre. -/
theorem tendsto_pairCompatibleReceiverTransportPhase
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
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVorticityFourierMode solution t) output))
      atTop
      (nhds ((1 / 2 : ℂ) *
        (completeReceiverTransportFirstPhaseAtOutput solution t output +
          conj (completeReceiverTransportFirstPhaseAtOutput solution t output)))) := by
  have hfirst := tendsto_sum_pairCompatibleFrequencyAperture output
    (summable_norm_completeReceiverTransportFirstPhaseAtOutput
      solution t output).of_norm
  have hconj : Tendsto
      (fun radius : ℕ ↦ conj
        (∑ parent ∈ pairCompatibleFrequencyAperture output radius,
          completeOpenVorticityTransportFace solution t
            (parent, output - parent))) atTop
      (nhds (conj (completeReceiverTransportFirstPhaseAtOutput
        solution t output))) := by
    apply Tendsto.congr' _
      (Complex.continuous_conj.continuousAt.tendsto.comp hfirst)
    exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hsum := hfirst.add hconj
  have hconstant : Tendsto (fun _ : ℕ ↦ (1 / 2 : ℂ)) atTop
      (nhds (1 / 2 : ℂ)) := tendsto_const_nhds
  have hscaled := hconstant.mul hsum
  simpa only [
    complexVectorSymmetricPhasePairing_finiteAdvectiveCoefficient_eq_faceSum,
    completeReceiverTransportFirstPhaseAtOutput] using hscaled

/-! ## Complete output support and global reindex -/

/-- The cumulative multiplier vanishes outside the declared finite native output aperture. -/
theorem finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture
    (depth : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ smoothDyadicBandNativeAperture depth) :
    finiteDepthBoundaryWeight depth frequency = 0 := by
  have hdepth :
      frequency ∉ frequencyCube (dyadicHodgeOuterCutoff depth) := by
    intro hmem
    exact hfrequency (frequencyCube_mono (dyadicHodgeOuterCutoff_mono depth) hmem)
  have hzeroCutoff :
      dyadicHodgeOuterCutoff 0 ≤ dyadicHodgeOuterCutoff depth := by
    rw [dyadicHodgeOuterCutoff_eq, dyadicHodgeOuterCutoff_eq]
    apply Nat.sub_le_sub_right
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzero : frequency ∉ frequencyCube (dyadicHodgeOuterCutoff 0) := by
    intro hmem
    exact hfrequency (frequencyCube_mono
      (hzeroCutoff.trans (dyadicHodgeOuterCutoff_mono depth)) hmem)
  unfold finiteDepthBoundaryWeight
  rw [tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter depth) (by
        simpa only [dyadicHodgeOuterCutoff] using hdepth),
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter 0) (by
        simpa only [dyadicHodgeOuterCutoff] using hzero),
    sub_self]

/-- Output/parent coordinates and closed transported/receiver coordinates are equivalent without
discarding either occurrence. -/
def outputParentTransportEquiv :
    (SpatialFrequency × SpatialFrequency) ≃ CompleteTransportAddress where
  toFun pair := (pair.2, pair.1 - pair.2)
  invFun address := (address.1 + address.2, address.1)
  left_inv := by
    intro pair
    ext
    · simp only [Pi.add_apply, Pi.sub_apply]
      abel
    · rfl
  right_inv := by
    intro address
    ext
    · rfl
    · simp only [Pi.add_apply, Pi.sub_apply]
      abel

@[simp]
theorem outputParentTransportEquiv_apply_first
    (pair : SpatialFrequency × SpatialFrequency) :
    (outputParentTransportEquiv pair).1 = pair.2 := rfl

@[simp]
theorem outputParentTransportEquiv_apply_second
    (pair : SpatialFrequency × SpatialFrequency) :
    (outputParentTransportEquiv pair).2 = pair.1 - pair.2 := rfl

/-- The complete first-phase receiver work with the exact finite output support. -/
def completeReceiverTransportWeightedFirstPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑ output ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth output : ℂ) *
      completeReceiverTransportFirstPhaseAtOutput solution t output

/-- Every output-parent first-phase population is absolutely summable. -/
theorem summable_completeReceiverTransportWeightedFirstPhasePopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Summable fun pair : SpatialFrequency × SpatialFrequency ↦
      (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
        completeOpenVorticityTransportFace solution t
          (pair.2, pair.1 - pair.2) := by
  have haddress : Summable fun address : CompleteTransportAddress ↦
      (finiteDepthBoundaryWeight depth (address.1 + address.2) : ℂ) *
        completeOpenVorticityTransportFace solution t address := by
    apply Summable.of_norm
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
      (summable_norm_completeOpenVorticityTransportFace solution t)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_finiteDepthBoundaryWeight_le_one depth (address.1 + address.2))
  have hpull := haddress.comp_injective outputParentTransportEquiv.injective
  apply hpull.congr
  intro pair
  change
    (finiteDepthBoundaryWeight depth (pair.2 + (pair.1 - pair.2)) : ℂ) *
        completeOpenVorticityTransportFace solution t
          (pair.2, pair.1 - pair.2) =
      (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
        completeOpenVorticityTransportFace solution t
          (pair.2, pair.1 - pair.2)
  rw [show pair.2 + (pair.1 - pair.2) = pair.1 by
    ext coordinate
    simp only [Pi.add_apply, Pi.sub_apply]
    abel]

/-- The finite supported output sum is the complete double first-phase sum. -/
theorem completeReceiverTransportWeightedFirstPhase_eq_tsum_output_parent
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeReceiverTransportWeightedFirstPhase solution t depth =
      ∑' pair : SpatialFrequency × SpatialFrequency,
        (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
          completeOpenVorticityTransportFace solution t
            (pair.2, pair.1 - pair.2) := by
  let population : SpatialFrequency × SpatialFrequency → ℂ := fun pair ↦
    (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
      completeOpenVorticityTransportFace solution t
        (pair.2, pair.1 - pair.2)
  have hpopulation : Summable population :=
    summable_completeReceiverTransportWeightedFirstPhasePopulation
      solution t depth
  have hfiber (output : SpatialFrequency) : Summable fun parent ↦
      population (output, parent) := by
    apply hpopulation.comp_injective
    intro left right heq
    exact congrArg Prod.snd heq
  have hprod := hpopulation.tsum_prod' hfiber
  rw [hprod]
  rw [tsum_eq_sum (s := smoothDyadicBandNativeAperture depth) (fun output houtput ↦ by
    have hweight := finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture
      depth houtput
    simp [population, hweight])]
  unfold completeReceiverTransportWeightedFirstPhase
  apply Finset.sum_congr rfl
  intro output _houtput
  unfold completeReceiverTransportFirstPhaseAtOutput
  rw [← tsum_mul_left]

/-- Exchanging the transported and receiving pins turns the complete receiver first phase into
the negative cumulative transported-pin contribution. -/
theorem completeReceiverTransportWeightedFirstPhase_eq_neg_cumulative
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeReceiverTransportWeightedFirstPhase solution t depth =
      -completeCumulativeTransportContribution solution t depth := by
  rw [completeReceiverTransportWeightedFirstPhase_eq_tsum_output_parent]
  let face : CompleteTransportAddress → ℂ :=
    completeOpenVorticityTransportFace solution t
  let weighted : CompleteTransportAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth address.2 : ℂ) * face address
  have hrecoordinate :
      (∑' pair : SpatialFrequency × SpatialFrequency,
        (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
          face (pair.2, pair.1 - pair.2)) =
        ∑' address : CompleteTransportAddress,
          (finiteDepthBoundaryWeight depth
            (completeTransportReceiver address) : ℂ) * face address := by
    let receiverWeighted : CompleteTransportAddress → ℂ := fun address ↦
      (finiteDepthBoundaryWeight depth
        (completeTransportReceiver address) : ℂ) * face address
    calc
      (∑' pair : SpatialFrequency × SpatialFrequency,
          (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
            face (pair.2, pair.1 - pair.2)) =
          ∑' pair : SpatialFrequency × SpatialFrequency,
            receiverWeighted (outputParentTransportEquiv pair) := by
              apply tsum_congr
              intro pair
              simp only [receiverWeighted]
              have hreceiver :
                  completeTransportReceiver
                    (outputParentTransportEquiv pair) = -pair.1 := by
                change completeTransportReceiver
                    (pair.2, pair.1 - pair.2) = -pair.1
                unfold completeTransportReceiver
                ext coordinate
                simp only [Pi.neg_apply, Pi.sub_apply]
                abel
              rw [hreceiver, finiteDepthBoundaryWeight_neg]
              rfl
      _ = ∑' address : CompleteTransportAddress, receiverWeighted address :=
        outputParentTransportEquiv.tsum_eq receiverWeighted
      _ = ∑' address : CompleteTransportAddress,
          (finiteDepthBoundaryWeight depth
            (completeTransportReceiver address) : ℂ) * face address := rfl
  have hreindex :
      (∑' address, weighted (completeTransportExchange address)) =
        ∑' address, weighted address :=
    completeTransportExchange.tsum_eq weighted
  have hpoint (address : CompleteTransportAddress) :
      weighted (completeTransportExchange address) =
        -((finiteDepthBoundaryWeight depth
            (completeTransportReceiver address) : ℂ) * face address) := by
    simp only [weighted, completeTransportExchange_second,
      completeOpenVorticityTransportFace_exchange, face]
    ring
  change (∑' pair : SpatialFrequency × SpatialFrequency,
      (finiteDepthBoundaryWeight depth pair.1 : ℂ) *
        face (pair.2, pair.1 - pair.2)) = -(∑' address, weighted address)
  rw [hrecoordinate]
  calc
    (∑' address,
        (finiteDepthBoundaryWeight depth (completeTransportReceiver address) : ℂ) *
          face address) =
        -(∑' address, weighted (completeTransportExchange address)) := by
          rw [← tsum_neg]
          apply tsum_congr
          intro address
          simp only [hpoint, neg_neg]
    _ = -(∑' address, weighted address) := by rw [hreindex]

/-! ## Symmetric receiver target and the actual cofinal bridge -/

/-- The complete receiver work retains both Hermitian phases explicitly. -/
def completeSymmetricReceiverTransportWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑ output ∈ smoothDyadicBandNativeAperture depth,
    (finiteDepthBoundaryWeight depth output : ℂ) *
      ((1 / 2 : ℂ) *
        (completeReceiverTransportFirstPhaseAtOutput solution t output +
          conj (completeReceiverTransportFirstPhaseAtOutput solution t output)))

/-- The complete symmetric receiver is precisely the negative Hermitian symmetrization of the
transported-pin cumulative contribution. -/
theorem completeSymmetricReceiverTransportWork_eq_neg_cumulative_symmetrization
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeSymmetricReceiverTransportWork solution t depth =
      -(1 / 2 : ℂ) *
        (completeCumulativeTransportContribution solution t depth +
          conj (completeCumulativeTransportContribution solution t depth)) := by
  have hfirst := completeReceiverTransportWeightedFirstPhase_eq_neg_cumulative
    solution t depth
  have hscale :
      completeSymmetricReceiverTransportWork solution t depth =
        (1 / 2 : ℂ) *
          (∑ output ∈ smoothDyadicBandNativeAperture depth,
            (finiteDepthBoundaryWeight depth output : ℂ) *
              (completeReceiverTransportFirstPhaseAtOutput solution t output +
                conj (completeReceiverTransportFirstPhaseAtOutput solution t output))) := by
    unfold completeSymmetricReceiverTransportWork
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _houtput
    ring
  have hrearrange :
      (∑ output ∈ smoothDyadicBandNativeAperture depth,
        (finiteDepthBoundaryWeight depth output : ℂ) *
          (completeReceiverTransportFirstPhaseAtOutput solution t output +
            conj (completeReceiverTransportFirstPhaseAtOutput solution t output))) =
        completeReceiverTransportWeightedFirstPhase solution t depth +
          conj (completeReceiverTransportWeightedFirstPhase solution t depth) := by
    unfold completeReceiverTransportWeightedFirstPhase
    rw [map_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro output _houtput
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [hscale, hrearrange, hfirst]
  simp only [map_neg]
  ring

/-- **Cofinal receiver-work join.**  The actual finite pair-compatible receiver transport work
converges to the negative Hermitian symmetrization of the complete cumulative transport
contribution.  Output support is finite; interaction exchange is used only after passage to the
absolutely summable complete population. -/
theorem tendsto_finitePairCompatibleReceiverTransportWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleReceiverTransportWork solution t depth radius)
      atTop
      (nhds (-(1 / 2 : ℂ) *
        (completeCumulativeTransportContribution solution t depth +
          conj (completeCumulativeTransportContribution solution t depth)))) := by
  have hlimit : Tendsto
      (fun radius : ℕ ↦
        finitePairCompatibleReceiverTransportWork solution t depth radius)
      atTop
      (nhds (completeSymmetricReceiverTransportWork solution t depth)) := by
    unfold finitePairCompatibleReceiverTransportWork
      completeSymmetricReceiverTransportWork
    apply tendsto_finsetSum
    intro output _houtput
    exact tendsto_const_nhds.mul
      (tendsto_pairCompatibleReceiverTransportPhase solution t output)
  simpa only [completeSymmetricReceiverTransportWork_eq_neg_cumulative_symmetrization]
    using hlimit

/-- The depth-cofinal complete receiver transport work returns the Hermitian low-pass boundary.
The complete transported-pin contribution tends to the negative low-pass face, and the receiver
exchange contributes the second exact sign. -/
theorem tendsto_completeSymmetricReceiverTransportWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto (completeSymmetricReceiverTransportWork solution t) atTop
      (nhds ((1 / 2 : ℂ) *
        (completeLowPassTransportBoundary solution t +
          conj (completeLowPassTransportBoundary solution t)))) := by
  have hcumulative :=
    tendsto_completeCumulativeTransportContribution_actual_atTop solution t
  have hconjugate : Tendsto
      (fun depth : ℕ ↦ conj
        (completeCumulativeTransportContribution solution t depth)) atTop
      (nhds (conj (-completeLowPassTransportBoundary solution t))) :=
    Complex.continuous_conj.continuousAt.tendsto.comp hcumulative
  have hsum := hcumulative.add hconjugate
  have hconstant : Tendsto (fun _ : ℕ ↦ -(1 / 2 : ℂ)) atTop
      (nhds (-(1 / 2 : ℂ))) := tendsto_const_nhds
  have hscaled := hconstant.mul hsum
  have htarget :
      -(1 / 2 : ℂ) *
          (-completeLowPassTransportBoundary solution t +
            conj (-completeLowPassTransportBoundary solution t)) =
        (1 / 2 : ℂ) *
          (completeLowPassTransportBoundary solution t +
            conj (completeLowPassTransportBoundary solution t)) := by
    simp only [map_neg]
    ring
  rw [htarget] at hscaled
  apply Tendsto.congr' _ hscaled
  filter_upwards [] with depth
  exact (completeSymmetricReceiverTransportWork_eq_neg_cumulative_symmetrization
    solution t depth).symm

end Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
