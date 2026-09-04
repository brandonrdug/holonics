import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeProductFaces
import ElementaryHolonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation

/-!
# Two-axis mass of the direct dyadic Hodge coefficient

**[proved-derived]** This owner reindexes the genuine zero-padded first/second-coordinate
`Δ² × Δ²` receiver into the global lattice chart used by the exact nine-face Hodge product rule.
The two left aperture residues, the two right aperture residues, and the zero crossing remain in
the same coefficient population.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeProductFaces

/-- The genuine direct scalar/Hodge product before natural-index aperture reindexing. -/
def directDyadicHodgeCoefficient
    (scale : ℕ) (component coordinate input : Fin 3)
    (frequency : SpatialFrequency) : ℂ :=
  directDyadicScalarCoefficient scale frequency *
    hodgeJacobianMultiplierEntry frequency component coordinate input

/-- The forward-stencil base associated to a zero-padded backward-difference address.  Natural
address `index` is transported to lattice address `index - 2`, with the subtraction performed in
`ℤ`; hence addresses `0` and `1` are the two genuine left aperture residues. -/
def dyadicHodgeBackwardPaddedFrequency
    (scale firstIndex secondIndex thirdIndex : ℕ) : SpatialFrequency :=
  ![(firstIndex : ℤ) - (dyadicHodgeApertureRadius scale : ℤ) - 2,
    (secondIndex : ℤ) - (dyadicHodgeApertureRadius scale : ℤ) - 2,
    centeredFrequency (dyadicHodgeApertureRadius scale) thirdIndex]

theorem dyadicHodgeBackwardPaddedFrequency_first_succ
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeBackwardPaddedFrequency scale (firstIndex + 1) secondIndex thirdIndex =
      dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex +
        coordinateStep 0 := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeBackwardPaddedFrequency, coordinateStep, Pi.single_apply] <;>
    omega

theorem dyadicHodgeBackwardPaddedFrequency_second_succ
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeBackwardPaddedFrequency scale firstIndex (secondIndex + 1) thirdIndex =
      dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex +
        coordinateStep 1 := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeBackwardPaddedFrequency, coordinateStep, Pi.single_apply] <;>
    omega

theorem dyadicHodgeBackwardPaddedFrequency_second_succ_left
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    coordinateStep 1 +
        dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex =
      dyadicHodgeBackwardPaddedFrequency scale firstIndex (secondIndex + 1) thirdIndex := by
  rw [add_comm]
  exact (dyadicHodgeBackwardPaddedFrequency_second_succ
    scale firstIndex secondIndex thirdIndex).symm

theorem dyadicHodgeBackwardPaddedFrequency_second_add_two_right
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex +
        coordinateStep 1 * 2 =
      dyadicHodgeBackwardPaddedFrequency scale firstIndex (secondIndex + 2) thirdIndex := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeBackwardPaddedFrequency, coordinateStep] <;>
    omega

theorem dyadicHodgeBackwardPaddedFrequency_second_add_two_left
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    coordinateStep 1 * 2 +
        dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex =
      dyadicHodgeBackwardPaddedFrequency scale firstIndex (secondIndex + 2) thirdIndex := by
  rw [add_comm]
  exact dyadicHodgeBackwardPaddedFrequency_second_add_two_right
    scale firstIndex secondIndex thirdIndex

@[simp]
theorem zeroPaddedSecondPreviousCoefficient_add_two
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient coefficient count (index + 2) =
      zeroPaddedCoefficient coefficient count index := by
  simp [zeroPaddedSecondPreviousCoefficient]

@[simp]
theorem zeroPaddedSecondPreviousCoefficient_add_one
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient coefficient count (index + 1) =
      zeroPaddedPreviousCoefficient coefficient count index := by
  by_cases hzero : index = 0
  · subst index
    simp [zeroPaddedSecondPreviousCoefficient, zeroPaddedPreviousCoefficient]
  · simp [zeroPaddedSecondPreviousCoefficient, zeroPaddedPreviousCoefficient, hzero]

theorem zeroPaddedCoefficient_secondCombination
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient
        (fun position ↦ first position - 2 * middle position + last position)
        count index =
      zeroPaddedCoefficient first count index -
          2 * zeroPaddedCoefficient middle count index +
        zeroPaddedCoefficient last count index := by
  unfold zeroPaddedCoefficient
  split_ifs <;> ring

theorem zeroPaddedPreviousCoefficient_secondCombination
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedPreviousCoefficient
        (fun position ↦ first position - 2 * middle position + last position)
        count index =
      zeroPaddedPreviousCoefficient first count index -
          2 * zeroPaddedPreviousCoefficient middle count index +
        zeroPaddedPreviousCoefficient last count index := by
  unfold zeroPaddedPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_secondCombination first middle last count (index - 1)

theorem zeroPaddedSecondPreviousCoefficient_secondCombination
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient
        (fun position ↦ first position - 2 * middle position + last position)
        count index =
      zeroPaddedSecondPreviousCoefficient first count index -
          2 * zeroPaddedSecondPreviousCoefficient middle count index +
        zeroPaddedSecondPreviousCoefficient last count index := by
  unfold zeroPaddedSecondPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_secondCombination first middle last count (index - 2)

theorem zeroPaddedCoefficient_secondCombination_right
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient
        (fun position ↦ first position - middle position * 2 + last position)
        count index =
      zeroPaddedCoefficient first count index -
          zeroPaddedCoefficient middle count index * 2 +
        zeroPaddedCoefficient last count index := by
  unfold zeroPaddedCoefficient
  split_ifs <;> ring

theorem zeroPaddedPreviousCoefficient_secondCombination_right
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedPreviousCoefficient
        (fun position ↦ first position - middle position * 2 + last position)
        count index =
      zeroPaddedPreviousCoefficient first count index -
          zeroPaddedPreviousCoefficient middle count index * 2 +
        zeroPaddedPreviousCoefficient last count index := by
  unfold zeroPaddedPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_secondCombination_right
      first middle last count (index - 1)

theorem zeroPaddedSecondPreviousCoefficient_secondCombination_right
    (first middle last : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient
        (fun position ↦ first position - middle position * 2 + last position)
        count index =
      zeroPaddedSecondPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient middle count index * 2 +
        zeroPaddedSecondPreviousCoefficient last count index := by
  unfold zeroPaddedSecondPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_secondCombination_right
      first middle last count (index - 2)

theorem zeroPaddedPreviousCoefficient_sub
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedPreviousCoefficient (fun position ↦ first position - second position)
        count index =
      zeroPaddedPreviousCoefficient first count index -
        zeroPaddedPreviousCoefficient second count index := by
  unfold zeroPaddedPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_sub first second count (index - 1)

theorem zeroPaddedSecondPreviousCoefficient_sub
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient
        (fun position ↦ first position - second position) count index =
      zeroPaddedSecondPreviousCoefficient first count index -
        zeroPaddedSecondPreviousCoefficient second count index := by
  unfold zeroPaddedSecondPreviousCoefficient
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_sub first second count (index - 2)

/-- The same padded-address reindex for the genuine direct scalar band. -/
theorem directDyadicScalarCoefficient_backwardPadded_eq_secondPrevious
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicScalarCoefficient scale
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      zeroPaddedSecondPreviousCoefficient
        (fun firstPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (fun secondPosition ↦
              dyadicTensorBandCubeCoefficient scale
                firstPosition secondPosition thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex)
        (dyadicHodgeApertureCount scale) firstIndex := by
  by_cases hfirstSmall : firstIndex < 2
  · have houtside :
        dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex ∉
          frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
      intro hmem
      have hcoordinate :=
        (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
      simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
      omega
    unfold directDyadicScalarCoefficient
    rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
    simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall]
  · by_cases hsecondSmall : secondIndex < 2
    · have houtside :
          dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex ∉
            frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
        intro hmem
        have hcoordinate :=
          (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
        simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
        omega
      unfold directDyadicScalarCoefficient
      rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
      simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
        zeroPaddedCoefficient]
    · by_cases hfirstInside :
          firstIndex - 2 < dyadicHodgeApertureCount scale
      · by_cases hsecondInside :
            secondIndex - 2 < dyadicHodgeApertureCount scale
        · have hfrequency :
              dyadicHodgeBackwardPaddedFrequency scale
                  firstIndex secondIndex thirdIndex =
                dyadicHodgeApertureFrequency scale
                  (firstIndex - 2) (secondIndex - 2) thirdIndex := by
            funext axis
            fin_cases axis <;>
              simp [dyadicHodgeBackwardPaddedFrequency,
                dyadicHodgeApertureFrequency, centeredFrequency] <;>
              omega
          rw [hfrequency]
          simpa [directDyadicScalarCoefficient,
            zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
            zeroPaddedCoefficient, hfirstInside, hsecondInside] using
            (dyadicTensorBandCubeCoefficient_eq_actual scale
              (firstIndex - 2) (secondIndex - 2) thirdIndex).symm
        · have houtside :
              dyadicHodgeBackwardPaddedFrequency scale
                  firstIndex secondIndex thirdIndex ∉
                frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
            intro hmem
            have hcoordinate :=
              (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
            unfold dyadicHodgeApertureCount centeredFrequencyCount
              dyadicHodgeApertureRadius at hsecondInside
            simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
            omega
          unfold directDyadicScalarCoefficient
          rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
          simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
            zeroPaddedCoefficient, hfirstInside, hsecondInside]
      · have houtside :
            dyadicHodgeBackwardPaddedFrequency scale
                firstIndex secondIndex thirdIndex ∉
              frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
          intro hmem
          have hcoordinate :=
            (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
          unfold dyadicHodgeApertureCount centeredFrequencyCount
            dyadicHodgeApertureRadius at hfirstInside
          simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
          omega
        unfold directDyadicScalarCoefficient
        rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
        simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
          zeroPaddedCoefficient, hfirstInside]

theorem zeroPaddedVariation_sub
    (order : ℕ) (horder : order ≤ 2)
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedVariation order (fun position ↦ first position - second position)
        count index =
      zeroPaddedVariation order first count index -
        zeroPaddedVariation order second count index := by
  interval_cases order
  · rfl
  · exact zeroPaddedBackwardDifference_sub first second count index
  · exact zeroPaddedSecondDifference_sub first second count index

theorem zeroPaddedVariation_mul_right
    (order : ℕ) (horder : order ≤ 2)
    (coefficient : ℕ → ℂ) (constant : ℂ) (count index : ℕ) :
    zeroPaddedVariation order (fun position ↦ coefficient position * constant)
        count index =
      zeroPaddedVariation order coefficient count index * constant := by
  interval_cases order
  · rfl
  · exact zeroPaddedBackwardDifference_mul_right coefficient constant count index
  · exact zeroPaddedSecondDifference_mul_right coefficient constant count index

theorem zeroPaddedVariation_separatedTensorCoefficient
    (firstOrder secondOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    zeroPaddedVariation firstOrder
        (fun firstPosition ↦
          zeroPaddedVariation secondOrder
            (fun secondPosition ↦ separatedTensorCoefficient first second third
              firstPosition secondPosition thirdIndex)
            count secondIndex)
        count firstIndex =
      separatedTensorCoefficient
        (fun position ↦ zeroPaddedVariation firstOrder first count position)
        (fun position ↦ zeroPaddedVariation secondOrder second count position)
        third firstIndex secondIndex thirdIndex := by
  have hinner :
      (fun firstPosition ↦
        zeroPaddedVariation secondOrder
          (fun secondPosition ↦ separatedTensorCoefficient first second third
            firstPosition secondPosition thirdIndex)
          count secondIndex) =
        fun firstPosition ↦ first firstPosition *
          (zeroPaddedVariation secondOrder second count secondIndex *
            third thirdIndex) := by
    funext firstPosition
    have hfunction :
        (fun secondPosition ↦ separatedTensorCoefficient first second third
          firstPosition secondPosition thirdIndex) =
          fun secondPosition ↦ second secondPosition *
            (first firstPosition * third thirdIndex) := by
      funext secondPosition
      simp [separatedTensorCoefficient]
      ring
    rw [hfunction,
      zeroPaddedVariation_mul_right secondOrder hsecondOrder second
        (first firstPosition * third thirdIndex) count secondIndex]
    ring
  rw [hinner]
  have houter := zeroPaddedVariation_mul_right firstOrder hfirstOrder first
    (zeroPaddedVariation secondOrder second count secondIndex * third thirdIndex)
    count firstIndex
  rw [houter]
  unfold separatedTensorCoefficient
  ring

/-- Natural-index subset variation of the single direct scalar cube. -/
def dyadicTensorBandCubeSubsetVariation
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedVariation firstOrder
    (fun firstPosition ↦
      zeroPaddedVariation secondOrder
        (fun secondPosition ↦ dyadicTensorBandCubeCoefficient scale
          firstPosition secondPosition thirdIndex)
        (dyadicHodgeApertureCount scale) secondIndex)
    (dyadicHodgeApertureCount scale) firstIndex

/-- The direct-cube variation is exactly the already bounded next-minus-base tensor subset. -/
theorem dyadicTensorBandCubeSubsetVariation_eq
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2) :
    dyadicTensorBandCubeSubsetVariation scale firstOrder secondOrder
        firstIndex secondIndex thirdIndex =
      dyadicTensorBandSubsetVariation scale firstOrder secondOrder
        firstIndex secondIndex thirdIndex := by
  unfold dyadicTensorBandCubeSubsetVariation dyadicTensorBandCubeCoefficient
  have hinner :
      (fun firstPosition ↦
        zeroPaddedVariation secondOrder
          (fun secondPosition ↦
            dyadicNextTensorCubeCoefficient scale firstPosition secondPosition thirdIndex -
              dyadicBaseTensorCubeCoefficient scale firstPosition secondPosition thirdIndex)
          (dyadicHodgeApertureCount scale) secondIndex) =
        fun firstPosition ↦
          zeroPaddedVariation secondOrder
              (fun secondPosition ↦
                dyadicNextTensorCubeCoefficient scale
                  firstPosition secondPosition thirdIndex)
              (dyadicHodgeApertureCount scale) secondIndex -
            zeroPaddedVariation secondOrder
              (fun secondPosition ↦
                dyadicBaseTensorCubeCoefficient scale
                  firstPosition secondPosition thirdIndex)
              (dyadicHodgeApertureCount scale) secondIndex := by
    funext firstPosition
    exact zeroPaddedVariation_sub secondOrder hsecondOrder _ _ _ _
  rw [hinner, zeroPaddedVariation_sub firstOrder hfirstOrder]
  rw [show dyadicNextTensorCubeCoefficient scale =
      separatedTensorCoefficient (dyadicNextCoordinateSlice scale)
        (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale) by rfl,
    show dyadicBaseTensorCubeCoefficient scale =
      separatedTensorCoefficient (dyadicBaseCoordinateSlice scale)
        (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale) by rfl,
    zeroPaddedVariation_separatedTensorCoefficient firstOrder secondOrder
      hfirstOrder hsecondOrder,
    zeroPaddedVariation_separatedTensorCoefficient firstOrder secondOrder
      hfirstOrder hsecondOrder]
  rfl

/-- Padded global base whose order-`(a,b)` forward face ends at natural subset address
`(firstIndex, secondIndex)`. -/
def dyadicHodgeSubsetPaddedFrequency
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ) :
    SpatialFrequency :=
  dyadicHodgeBackwardPaddedFrequency scale
    (firstIndex + (2 - firstOrder)) (secondIndex + (2 - secondOrder)) thirdIndex

/-- Every admitted scalar forward face is exactly its bounded natural-index subset variation. -/
theorem mixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + firstOrder)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + secondOrder) :
    mixedForwardDifference 0 1 firstOrder secondOrder
        (directDyadicScalarCoefficient scale)
        (dyadicHodgeSubsetPaddedFrequency scale firstOrder secondOrder
          firstIndex secondIndex thirdIndex) =
      dyadicTensorBandSubsetVariation scale firstOrder secondOrder
        firstIndex secondIndex thirdIndex := by
  rw [← dyadicTensorBandCubeSubsetVariation_eq scale firstOrder secondOrder
    firstIndex secondIndex thirdIndex hfirstOrder hsecondOrder]
  unfold dyadicHodgeSubsetPaddedFrequency
  interval_cases firstOrder <;> interval_cases secondOrder <;>
    simp only [Nat.reduceSubDiff, Nat.add_zero, Nat.add_one,
      mixedForwardDifference, Function.iterate_succ_apply',
      Function.iterate_zero_apply, fwdDiff]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_first_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals
    simp_rw [directDyadicScalarCoefficient_backwardPadded_eq_secondPrevious]
  all_goals
    simp only [zeroPaddedSecondPreviousCoefficient_add_two,
      zeroPaddedSecondPreviousCoefficient_add_one]
  all_goals unfold dyadicTensorBandCubeSubsetVariation zeroPaddedVariation
  all_goals
    simp only [zeroPaddedBackwardDifference_eq_current_sub_previous,
      zeroPaddedSecondDifference_eq_three_coefficients]
  case «0».«0» =>
    have hfirst : firstIndex < dyadicHodgeApertureCount scale := by omega
    have hsecond : secondIndex < dyadicHodgeApertureCount scale := by omega
    simp only [zeroPaddedCoefficient, if_pos hfirst, if_pos hsecond]
  case «0».«1» =>
    have hfirst : firstIndex < dyadicHodgeApertureCount scale := by omega
    simp only [zeroPaddedCoefficient, if_pos hfirst]
  case «0».«2» =>
    have hfirst : firstIndex < dyadicHodgeApertureCount scale := by omega
    simp only [zeroPaddedCoefficient, if_pos hfirst]
    ring
  case «1».«0» =>
    have hsecond : secondIndex < dyadicHodgeApertureCount scale := by omega
    simp only [zeroPaddedCoefficient, if_pos hsecond]
  case «1».«1» =>
    rw [zeroPaddedCoefficient_sub, zeroPaddedPreviousCoefficient_sub] <;> ring
  case «1».«2» =>
    rw [zeroPaddedCoefficient_secondCombination,
      zeroPaddedPreviousCoefficient_secondCombination] <;> ring
  case «2».«0» =>
    have hsecond : secondIndex < dyadicHodgeApertureCount scale := by omega
    simp only [zeroPaddedCoefficient, if_pos hsecond]
    ring
  case «2».«1» =>
    rw [zeroPaddedCoefficient_sub, zeroPaddedPreviousCoefficient_sub,
      zeroPaddedSecondPreviousCoefficient_sub] <;> ring
  case «2».«2» =>
    rw [zeroPaddedCoefficient_secondCombination,
      zeroPaddedPreviousCoefficient_secondCombination,
      zeroPaddedSecondPreviousCoefficient_secondCombination] <;> ring

/-- Exchanging the two displayed coordinates exchanges the two subset orders.  This is an exact
tensor symmetry, including every zero-extension boundary value. -/
theorem dyadicTensorBandSubsetVariation_swap
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ) :
    dyadicTensorBandSubsetVariation scale firstOrder secondOrder
        firstIndex secondIndex thirdIndex =
      dyadicTensorBandSubsetVariation scale secondOrder firstOrder
        secondIndex firstIndex thirdIndex := by
  unfold dyadicTensorBandSubsetVariation separatedDyadicProfileSubsetVariation
    separatedTensorCoefficient
  ring

theorem sum_norm_dyadicTensorBandSubsetVariation_zero_one_le_512_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 0 1
            firstIndex secondIndex thirdIndex‖) ≤
      512 * (dyadicRadius scale : ℝ) ^ 2 := by
  rw [Finset.sum_comm]
  simpa only [dyadicTensorBandSubsetVariation_swap] using
    sum_norm_dyadicTensorBandSubsetVariation_one_zero_le_512_mul scale

theorem sum_norm_dyadicTensorBandSubsetVariation_zero_two_le_384_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 0 2
            firstIndex secondIndex thirdIndex‖) ≤
      384 * (dyadicRadius scale : ℝ) := by
  rw [Finset.sum_comm]
  simpa only [dyadicTensorBandSubsetVariation_swap] using
    sum_norm_dyadicTensorBandSubsetVariation_two_zero_le_384_mul scale

/-- A scalar forward face whose base still lies in the left first-coordinate pad is exactly zero.
This is the residue needed to translate the global face population to natural subset indices. -/
theorem mixedForwardDifference_directDyadicScalarCoefficient_eq_zero_of_first_lt
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hfirstIndex : firstIndex < 2 - firstOrder) :
    mixedForwardDifference 0 1 firstOrder secondOrder
        (directDyadicScalarCoefficient scale)
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) = 0 := by
  interval_cases firstOrder <;> interval_cases secondOrder
  all_goals try omega
  all_goals
    simp only [mixedForwardDifference, Function.iterate_succ_apply',
      Function.iterate_zero_apply, fwdDiff]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_first_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals simp_rw [directDyadicScalarCoefficient_backwardPadded_eq_secondPrevious]
  all_goals simp_all [zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient] <;> ring

/-- The corresponding exact zero residue in the second displayed coordinate. -/
theorem mixedForwardDifference_directDyadicScalarCoefficient_eq_zero_of_second_lt
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hsecondIndex : secondIndex < 2 - secondOrder) :
    mixedForwardDifference 0 1 firstOrder secondOrder
        (directDyadicScalarCoefficient scale)
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) = 0 := by
  interval_cases firstOrder <;> interval_cases secondOrder
  all_goals try omega
  all_goals
    simp only [mixedForwardDifference, Function.iterate_succ_apply',
      Function.iterate_zero_apply, fwdDiff]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_first_succ]
  all_goals try simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ]
  all_goals simp_rw [directDyadicScalarCoefficient_backwardPadded_eq_secondPrevious]
  all_goals simp_all [zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient] <;> ring

/-- One of the nine exact product faces, indexed by the natural zero-padded scalar variation
address.  The complementary Hodge face starts at the terminal pin of the scalar face. -/
def dyadicHodgeSubsetProductFace
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  let frequency := dyadicHodgeSubsetPaddedFrequency scale firstOrder secondOrder
    firstIndex secondIndex thirdIndex
  mixedForwardDifference 0 1 firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency *
    mixedForwardDifference 0 1 (2 - firstOrder) (2 - secondOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint 0 1 frequency firstOrder secondOrder)

/-- The same exact product face in the global backward-padded address chart used by the actual
zero-padded `Δ² × Δ²` receiver. -/
def dyadicHodgeGlobalProductFace
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  let frequency := dyadicHodgeBackwardPaddedFrequency scale
    firstIndex secondIndex thirdIndex
  mixedForwardDifference 0 1 firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency *
    mixedForwardDifference 0 1 (2 - firstOrder) (2 - secondOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint 0 1 frequency firstOrder secondOrder)

/-- Total mass of one global Leibniz face on the exact doubly padded cube. -/
def dyadicHodgeGlobalProductFaceMass
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3) : ℝ :=
  ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
    ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ‖dyadicHodgeGlobalProductFace scale firstOrder secondOrder
          component coordinate input firstIndex secondIndex thirdIndex‖

/-- Weighted norm population emitted by the exact nine-face Leibniz rule. -/
def dyadicHodgeGlobalLeibnizNormMajorant
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℝ :=
  ‖dyadicHodgeGlobalProductFace scale 2 2 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (2 * ‖dyadicHodgeGlobalProductFace scale 1 2 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (‖dyadicHodgeGlobalProductFace scale 0 2 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (2 * ‖dyadicHodgeGlobalProductFace scale 2 1 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (4 * ‖dyadicHodgeGlobalProductFace scale 1 1 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (2 * ‖dyadicHodgeGlobalProductFace scale 0 1 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (‖dyadicHodgeGlobalProductFace scale 2 0 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
    (2 * ‖dyadicHodgeGlobalProductFace scale 1 0 component coordinate input
      firstIndex secondIndex thirdIndex‖ +
     ‖dyadicHodgeGlobalProductFace scale 0 0 component coordinate input
      firstIndex secondIndex thirdIndex‖)))))))

theorem dyadicHodgeGlobalProductFace_add_offsets_eq_subset
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeGlobalProductFace scale firstOrder secondOrder
        component coordinate input
        (firstIndex + (2 - firstOrder)) (secondIndex + (2 - secondOrder))
        thirdIndex =
      dyadicHodgeSubsetProductFace scale firstOrder secondOrder
        component coordinate input firstIndex secondIndex thirdIndex := by
  rfl

theorem dyadicHodgeGlobalProductFace_eq_zero_of_first_lt
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hfirstIndex : firstIndex < 2 - firstOrder) :
    dyadicHodgeGlobalProductFace scale firstOrder secondOrder
        component coordinate input firstIndex secondIndex thirdIndex = 0 := by
  simp only [dyadicHodgeGlobalProductFace]
  rw [mixedForwardDifference_directDyadicScalarCoefficient_eq_zero_of_first_lt
    scale firstOrder secondOrder firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hfirstIndex]
  simp

theorem dyadicHodgeGlobalProductFace_eq_zero_of_second_lt
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hsecondIndex : secondIndex < 2 - secondOrder) :
    dyadicHodgeGlobalProductFace scale firstOrder secondOrder
        component coordinate input firstIndex secondIndex thirdIndex = 0 := by
  simp only [dyadicHodgeGlobalProductFace]
  rw [mixedForwardDifference_directDyadicScalarCoefficient_eq_zero_of_second_lt
    scale firstOrder secondOrder firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hsecondIndex]
  simp

/-- Exact two-coordinate translation of a finite Fubini sum after retaining both left zero
residues. -/
theorem sum_range_twoAxis_shift_of_prefix_zero
    {α : Type*} [AddCommMonoid α]
    (firstOffset secondOffset firstCount secondCount : ℕ)
    (global subset : ℕ → ℕ → α)
    (hfirst : ∀ firstIndex < firstOffset,
      ∀ secondIndex < secondOffset + secondCount,
        global firstIndex secondIndex = 0)
    (hsecond : ∀ firstIndex < firstCount,
      ∀ secondIndex < secondOffset,
        global (firstOffset + firstIndex) secondIndex = 0)
    (hshift : ∀ firstIndex < firstCount,
      ∀ secondIndex < secondCount,
        global (firstOffset + firstIndex) (secondOffset + secondIndex) =
          subset firstIndex secondIndex) :
    (∑ firstIndex ∈ Finset.range (firstOffset + firstCount),
      ∑ secondIndex ∈ Finset.range (secondOffset + secondCount),
        global firstIndex secondIndex) =
      ∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          subset firstIndex secondIndex := by
  rw [Finset.sum_range_add]
  have hleft :
      (∑ firstIndex ∈ Finset.range firstOffset,
        ∑ secondIndex ∈ Finset.range (secondOffset + secondCount),
          global firstIndex secondIndex) = 0 := by
    apply Finset.sum_eq_zero
    intro firstIndex hfirstIndex
    apply Finset.sum_eq_zero
    intro secondIndex hsecondIndex
    exact hfirst firstIndex (Finset.mem_range.mp hfirstIndex)
      secondIndex (Finset.mem_range.mp hsecondIndex)
  rw [hleft, zero_add]
  apply Finset.sum_congr rfl
  intro firstIndex hfirstIndex
  rw [Finset.sum_range_add]
  have hbottom :
      (∑ secondIndex ∈ Finset.range secondOffset,
        global (firstOffset + firstIndex) secondIndex) = 0 := by
    apply Finset.sum_eq_zero
    intro secondIndex hsecondIndex
    exact hsecond firstIndex (Finset.mem_range.mp hfirstIndex)
      secondIndex (Finset.mem_range.mp hsecondIndex)
  rw [hbottom, zero_add]
  apply Finset.sum_congr rfl
  intro secondIndex hsecondIndex
  exact hshift firstIndex (Finset.mem_range.mp hfirstIndex)
    secondIndex (Finset.mem_range.mp hsecondIndex)

/-- The global nine-face chart and the natural subset chart have exactly the same total mass.
Both left aperture residues are proved zero and removed; no mode-count estimate occurs. -/
theorem sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeGlobalProductFace scale firstOrder secondOrder
            component coordinate input firstIndex secondIndex thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range
            (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicHodgeSubsetProductFace scale firstOrder secondOrder
              component coordinate input firstIndex secondIndex thirdIndex‖ := by
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    (2 - firstOrder) + (dyadicHodgeApertureCount scale + firstOrder) by omega]
  nth_rewrite 1 [show dyadicHodgeApertureCount scale + 2 =
    (2 - secondOrder) + (dyadicHodgeApertureCount scale + secondOrder) by omega]
  apply sum_range_twoAxis_shift_of_prefix_zero
  · intro firstIndex hfirstIndex secondIndex _hsecondIndex
    apply Finset.sum_eq_zero
    intro thirdIndex _hthirdIndex
    rw [dyadicHodgeGlobalProductFace_eq_zero_of_first_lt scale firstOrder
      secondOrder component coordinate input firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hfirstIndex]
    simp
  · intro firstIndex _hfirstIndex secondIndex hsecondIndex
    apply Finset.sum_eq_zero
    intro thirdIndex _hthirdIndex
    rw [dyadicHodgeGlobalProductFace_eq_zero_of_second_lt scale firstOrder
      secondOrder component coordinate input ((2 - firstOrder) + firstIndex)
      secondIndex thirdIndex hfirstOrder hsecondOrder hsecondIndex]
    simp
  · intro firstIndex _hfirstIndex secondIndex _hsecondIndex
    apply Finset.sum_congr rfl
    intro thirdIndex _hthirdIndex
    rw [show (2 - firstOrder) + firstIndex =
          firstIndex + (2 - firstOrder) by omega,
      show (2 - secondOrder) + secondIndex =
          secondIndex + (2 - secondOrder) by omega,
      dyadicHodgeGlobalProductFace_add_offsets_eq_subset]

/-- Explicit complementary rational-Hodge envelope for the nine Leibniz faces. -/
def dyadicHodgeComplementaryFaceBound
    (scale firstOrder secondOrder : ℕ) : ℝ :=
  match firstOrder, secondOrder with
  | 0, 0 => 32000000000 / (dyadicRadius scale : ℝ) ^ 4
  | 0, 1 => 166000000 / (dyadicRadius scale : ℝ) ^ 3
  | 0, 2 => 1300000 / (dyadicRadius scale : ℝ) ^ 2
  | 1, 0 => 166000000 / (dyadicRadius scale : ℝ) ^ 3
  | 1, 1 => 1200000 / (dyadicRadius scale : ℝ) ^ 2
  | 1, 2 => 14000 / (dyadicRadius scale : ℝ)
  | 2, 0 => 1300000 / (dyadicRadius scale : ℝ) ^ 2
  | 2, 1 => 14000 / (dyadicRadius scale : ℝ)
  | 2, 2 => 1
  | _, _ => 0

/-- Each actual subset product face is controlled by its scalar mass times the appropriate
complementary rational-Hodge envelope.  The proof uses the scalar face itself as the support pin,
so zero-crossing and aperture stencils are retained rather than discarded. -/
theorem norm_dyadicHodgeSubsetProductFace_le
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + firstOrder)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + secondOrder) :
    ‖dyadicHodgeSubsetProductFace scale firstOrder secondOrder
        component coordinate input firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicTensorBandSubsetVariation scale firstOrder secondOrder
          firstIndex secondIndex thirdIndex‖ *
        dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  let frequency := dyadicHodgeSubsetPaddedFrequency scale firstOrder secondOrder
    firstIndex secondIndex thirdIndex
  have hscalar :=
    mixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
      scale firstOrder secondOrder firstIndex secondIndex thirdIndex
      hfirstOrder hsecondOrder hfirstIndex hsecondIndex
  change ‖mixedForwardDifference 0 1 firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency *
    mixedForwardDifference 0 1 (2 - firstOrder) (2 - secondOrder)
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input)
      (twoAxisStencilPoint 0 1 frequency firstOrder secondOrder)‖ ≤ _
  change mixedForwardDifference 0 1 firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency = _ at hscalar
  rw [hscalar, norm_mul]
  by_cases hzero :
      dyadicTensorBandSubsetVariation scale firstOrder secondOrder
        firstIndex secondIndex thirdIndex = 0
  · simp [hzero]
  · have hglobal : mixedForwardDifference 0 1 firstOrder secondOrder
        (directDyadicScalarCoefficient scale) frequency ≠ 0 := by
      rw [hscalar]
      exact hzero
    gcongr
    interval_cases firstOrder <;> interval_cases secondOrder
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_two_two_le_of_scalar_zero_zero_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_two_one_le_of_scalar_zero_one_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_two_zero_le_of_scalar_zero_two_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_one_two_le_of_scalar_one_zero_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_one_one_le_of_scalar_one_one_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_one_zero_le_of_scalar_one_two_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_zero_two_le_of_scalar_two_zero_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_zero_one_le_of_scalar_two_one_ne_zero
          scale hscale 0 1 (by decide) frequency component coordinate input hglobal
    · simpa [dyadicHodgeComplementaryFaceBound, twoAxisStencilPoint] using
        norm_complementaryHodge_zero_zero_le_of_scalar_two_two_ne_zero
          0 1 frequency component coordinate input

/-- Fubini summation of one exact product face.  No cardinality bound is inserted: the right-hand
side is the already-controlled scalar variation mass times its complementary Hodge envelope. -/
theorem sum_norm_dyadicHodgeSubsetProductFace_le
    (scale firstOrder secondOrder : ℕ)
    (component coordinate input : Fin 3)
    (hscale : 3 ≤ scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2) :
    (∑ firstIndex ∈ Finset.range
        (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale firstOrder secondOrder
            component coordinate input firstIndex secondIndex thirdIndex‖) ≤
      (∑ firstIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range
            (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicTensorBandSubsetVariation scale firstOrder secondOrder
              firstIndex secondIndex thirdIndex‖) *
        dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder := by
  calc
    _ ≤ (∑ firstIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + firstOrder),
        ∑ secondIndex ∈ Finset.range
            (dyadicHodgeApertureCount scale + secondOrder),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicTensorBandSubsetVariation scale firstOrder secondOrder
              firstIndex secondIndex thirdIndex‖ *
              dyadicHodgeComplementaryFaceBound scale firstOrder secondOrder) := by
        gcongr with firstIndex hfirst secondIndex hsecond thirdIndex hthird
        exact norm_dyadicHodgeSubsetProductFace_le scale firstOrder secondOrder
          component coordinate input firstIndex secondIndex thirdIndex hscale
          hfirstOrder hsecondOrder (Finset.mem_range.mp hfirst)
          (Finset.mem_range.mp hsecond)
    _ = _ := by
      simp_rw [Finset.sum_mul]

theorem sum_norm_dyadicHodgeSubsetProductFace_zero_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 0 0 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      32768000000000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 0 0
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, Nat.add_zero]
  calc
    _ ≤ (1024 * (dyadicRadius scale : ℝ) ^ 3) *
        (32000000000 / (dyadicRadius scale : ℝ) ^ 4) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_zero_zero_le_1024_mul scale
    _ = 32768000000000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_zero_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 0 1 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      84992000000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 0 1
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, Nat.add_zero]
  calc
    _ ≤ (512 * (dyadicRadius scale : ℝ) ^ 2) *
        (166000000 / (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_zero_one_le_512_mul scale
    _ = 84992000000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_zero_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 0 2 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      499200000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 0 2
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, Nat.add_zero]
  calc
    _ ≤ (384 * (dyadicRadius scale : ℝ)) *
        (1300000 / (dyadicRadius scale : ℝ) ^ 2) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_zero_two_le_384_mul scale
    _ = 499200000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_one_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 1 0 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      84992000000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 1 0
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, Nat.add_zero]
  calc
    _ ≤ (512 * (dyadicRadius scale : ℝ) ^ 2) *
        (166000000 / (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_one_zero_le_512_mul scale
    _ = 84992000000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_one_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 1 1 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      307200000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 1 1
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound]
  calc
    _ ≤ (256 * (dyadicRadius scale : ℝ)) *
        (1200000 / (dyadicRadius scale : ℝ) ^ 2) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_one_one_le_256_mul scale
    _ = 307200000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_one_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 1 2 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      2688000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 1 2
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound]
  calc
    _ ≤ 192 * (14000 / (dyadicRadius scale : ℝ)) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_one_two_le_192 scale
    _ = 2688000 / (dyadicRadius scale : ℝ) := by ring

theorem sum_norm_dyadicHodgeSubsetProductFace_two_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 2 0 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      499200000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 2 0
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, Nat.add_zero]
  calc
    _ ≤ (384 * (dyadicRadius scale : ℝ)) *
        (1300000 / (dyadicRadius scale : ℝ) ^ 2) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_two_zero_le_384_mul scale
    _ = 499200000 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicHodgeSubsetProductFace_two_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 2 1 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      2688000 / (dyadicRadius scale : ℝ) := by
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 2 1
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound]
  calc
    _ ≤ 192 * (14000 / (dyadicRadius scale : ℝ)) := by
      gcongr
      exact sum_norm_dyadicTensorBandSubsetVariation_two_one_le_192 scale
    _ = 2688000 / (dyadicRadius scale : ℝ) := by ring

theorem sum_norm_dyadicHodgeSubsetProductFace_two_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeSubsetProductFace scale 2 2 component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      160 / (dyadicRadius scale : ℝ) := by
  refine (sum_norm_dyadicHodgeSubsetProductFace_le scale 2 2
    component coordinate input hscale (by omega) (by omega)).trans ?_
  simp only [dyadicHodgeComplementaryFaceBound, mul_one]
  exact sum_norm_dyadicTensorBandSubsetVariation_two_two_le_160_div scale

/-- A global coefficient at a padded address is exactly the doubly zero-padded coefficient two
positions earlier in each displayed coordinate.  This is the boundary-bearing reindex: it covers
all natural addresses, including both flanks beyond the finite aperture. -/
theorem directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hthird : thirdIndex < dyadicHodgeApertureCount scale) :
    directDyadicHodgeCoefficient scale component coordinate input
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      zeroPaddedSecondPreviousCoefficient
        (fun firstPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (fun secondPosition ↦
              dyadicHodgeCubeCoefficient scale component coordinate input
                firstPosition secondPosition thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex)
        (dyadicHodgeApertureCount scale) firstIndex := by
  by_cases hfirstSmall : firstIndex < 2
  · have houtside :
        dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex ∉
          frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
      intro hmem
      have hcoordinate :=
        (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
      simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
      omega
    unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
    rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
    simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall]
  · by_cases hsecondSmall : secondIndex < 2
    · have houtside :
          dyadicHodgeBackwardPaddedFrequency scale firstIndex secondIndex thirdIndex ∉
            frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
        intro hmem
        have hcoordinate :=
          (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
        simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius] at hcoordinate
        omega
      unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
      rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
      simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
        zeroPaddedCoefficient]
    · by_cases hfirstInside :
          firstIndex - 2 < dyadicHodgeApertureCount scale
      · by_cases hsecondInside :
            secondIndex - 2 < dyadicHodgeApertureCount scale
        · have hfrequency :
              dyadicHodgeBackwardPaddedFrequency scale
                  firstIndex secondIndex thirdIndex =
                dyadicHodgeApertureFrequency scale
                  (firstIndex - 2) (secondIndex - 2) thirdIndex := by
            funext axis
            fin_cases axis <;>
              simp [dyadicHodgeBackwardPaddedFrequency,
                dyadicHodgeApertureFrequency, centeredFrequency] <;>
              omega
          rw [hfrequency]
          simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
            zeroPaddedCoefficient, hfirstInside, hsecondInside,
            directDyadicHodgeCoefficient, directDyadicScalarCoefficient,
            dyadicHodgeCubeCoefficient]
        · have houtside :
              dyadicHodgeBackwardPaddedFrequency scale
                  firstIndex secondIndex thirdIndex ∉
                frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
            intro hmem
            have hcoordinate :=
              (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
            unfold dyadicHodgeApertureCount centeredFrequencyCount
              dyadicHodgeApertureRadius at hsecondInside
            simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius,
              dyadicHodgeApertureCount, centeredFrequencyCount] at hcoordinate
            omega
          unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
          rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
          simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
            zeroPaddedCoefficient, hfirstInside, hsecondInside]
      · have houtside :
            dyadicHodgeBackwardPaddedFrequency scale
                firstIndex secondIndex thirdIndex ∉
              frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
          intro hmem
          have hcoordinate :=
            (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
          unfold dyadicHodgeApertureCount centeredFrequencyCount
            dyadicHodgeApertureRadius at hfirstInside
          simp [dyadicHodgeBackwardPaddedFrequency, dyadicHodgeApertureRadius,
            dyadicHodgeApertureCount, centeredFrequencyCount] at hcoordinate
          omega
        unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
        rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
        simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
          zeroPaddedCoefficient, hfirstInside]

/-- The actual zero-padded `Δ² × Δ²` coefficient receiver in the first two displayed
coordinates. -/
def dyadicHodgeCubeSecondDifferenceFirstSecond
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceFirst
    (zeroPaddedSecondDifferenceSecond
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex

/-- The global mixed forward difference at the padded base is the exact nine-corner lattice
combination. -/
theorem mixedForwardDifference_two_two_directDyadicHodgeCoefficient_backwardPadded_eq
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    mixedForwardDifference 0 1 2 2
        (directDyadicHodgeCoefficient scale component coordinate input)
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 2) (secondIndex + 2) thirdIndex) -
        2 * directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 2) (secondIndex + 1) thirdIndex) +
        directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 2) secondIndex thirdIndex) -
        2 * directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 1) (secondIndex + 2) thirdIndex) +
        4 * directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 1) (secondIndex + 1) thirdIndex) -
        2 * directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            (firstIndex + 1) secondIndex thirdIndex) +
        directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            firstIndex (secondIndex + 2) thirdIndex) -
        2 * directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            firstIndex (secondIndex + 1) thirdIndex) +
        directDyadicHodgeCoefficient scale component coordinate input
          (dyadicHodgeBackwardPaddedFrequency scale
            firstIndex secondIndex thirdIndex) := by
  simp only [mixedForwardDifference, Function.iterate_succ_apply',
    Function.iterate_zero_apply, fwdDiff]
  simp_rw [← dyadicHodgeBackwardPaddedFrequency_second_succ,
    ← dyadicHodgeBackwardPaddedFrequency_first_succ,
    ← dyadicHodgeBackwardPaddedFrequency_second_succ]
  ring

/-- Exact reindex of the actual two-axis zero-padded receiver into the global lattice mixed
forward difference.  In particular, this is not an interior-only identity: addresses `0`, `1`,
`count`, and `count + 1` are all carried by the same equality. -/
theorem dyadicHodgeCubeSecondDifferenceFirstSecond_eq_mixedForwardDifference
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hthird : thirdIndex < dyadicHodgeApertureCount scale) :
    dyadicHodgeCubeSecondDifferenceFirstSecond scale component coordinate input
        firstIndex secondIndex thirdIndex =
      mixedForwardDifference 0 1 2 2
        (directDyadicHodgeCoefficient scale component coordinate input)
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) := by
  rw [mixedForwardDifference_two_two_directDyadicHodgeCoefficient_backwardPadded_eq]
  rw [directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 2) (secondIndex + 2)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 2) (secondIndex + 1)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 2) secondIndex
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 1) (secondIndex + 2)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 1) (secondIndex + 1)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input (firstIndex + 1) secondIndex
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input firstIndex (secondIndex + 2)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input firstIndex (secondIndex + 1)
          thirdIndex hthird,
    directDyadicHodgeCoefficient_backwardPadded_eq_secondPrevious
        scale component coordinate input firstIndex secondIndex thirdIndex hthird]
  simp only [zeroPaddedSecondPreviousCoefficient_add_two,
    zeroPaddedSecondPreviousCoefficient_add_one]
  unfold dyadicHodgeCubeSecondDifferenceFirstSecond
    zeroPaddedSecondDifferenceFirst zeroPaddedSecondDifferenceSecond
  simp only [zeroPaddedSecondDifference_eq_three_coefficients]
  rw [zeroPaddedCoefficient_secondCombination,
    zeroPaddedPreviousCoefficient_secondCombination,
    zeroPaddedSecondPreviousCoefficient_secondCombination]
  ring

/-- The genuine direct dyadic Hodge coefficient has exactly the nine global product faces of the
`Δ₀²Δ₁²` Leibniz rule. -/
theorem mixedForwardDifference_two_two_directDyadicHodgeCoefficient_eq_globalFaces
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    mixedForwardDifference 0 1 2 2
        (directDyadicHodgeCoefficient scale component coordinate input)
        (dyadicHodgeBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      dyadicHodgeGlobalProductFace scale 2 2 component coordinate input
          firstIndex secondIndex thirdIndex +
        2 * dyadicHodgeGlobalProductFace scale 1 2 component coordinate input
          firstIndex secondIndex thirdIndex +
        dyadicHodgeGlobalProductFace scale 0 2 component coordinate input
          firstIndex secondIndex thirdIndex +
        2 * dyadicHodgeGlobalProductFace scale 2 1 component coordinate input
          firstIndex secondIndex thirdIndex +
        4 * dyadicHodgeGlobalProductFace scale 1 1 component coordinate input
          firstIndex secondIndex thirdIndex +
        2 * dyadicHodgeGlobalProductFace scale 0 1 component coordinate input
          firstIndex secondIndex thirdIndex +
        dyadicHodgeGlobalProductFace scale 2 0 component coordinate input
          firstIndex secondIndex thirdIndex +
        2 * dyadicHodgeGlobalProductFace scale 1 0 component coordinate input
          firstIndex secondIndex thirdIndex +
        dyadicHodgeGlobalProductFace scale 0 0 component coordinate input
          firstIndex secondIndex thirdIndex := by
  rw [show directDyadicHodgeCoefficient scale component coordinate input =
      fun current ↦ directDyadicScalarCoefficient scale current *
        hodgeJacobianMultiplierEntry current component coordinate input by rfl,
    mixedForwardDifference_two_two_mul_eq]
  simp [dyadicHodgeGlobalProductFace, twoAxisStencilPoint,
    mixedForwardDifference]
  ring

/-- Pointwise triangle receiver for the actual zero-padded two-axis Hodge coefficient. -/
theorem norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le_globalFaces
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hthird : thirdIndex < dyadicHodgeApertureCount scale) :
    ‖dyadicHodgeCubeSecondDifferenceFirstSecond scale component coordinate input
        firstIndex secondIndex thirdIndex‖ ≤
      ‖dyadicHodgeGlobalProductFace scale 2 2 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖2 * dyadicHodgeGlobalProductFace scale 1 2 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖dyadicHodgeGlobalProductFace scale 0 2 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖2 * dyadicHodgeGlobalProductFace scale 2 1 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖4 * dyadicHodgeGlobalProductFace scale 1 1 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖2 * dyadicHodgeGlobalProductFace scale 0 1 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖dyadicHodgeGlobalProductFace scale 2 0 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
        (‖2 * dyadicHodgeGlobalProductFace scale 1 0 component coordinate input
          firstIndex secondIndex thirdIndex‖ +
         ‖dyadicHodgeGlobalProductFace scale 0 0 component coordinate input
          firstIndex secondIndex thirdIndex‖))))))) := by
  rw [dyadicHodgeCubeSecondDifferenceFirstSecond_eq_mixedForwardDifference
      scale component coordinate input firstIndex secondIndex thirdIndex hthird,
    mixedForwardDifference_two_two_directDyadicHodgeCoefficient_eq_globalFaces]
  rw [show
      dyadicHodgeGlobalProductFace scale 2 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          2 * dyadicHodgeGlobalProductFace scale 1 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          dyadicHodgeGlobalProductFace scale 0 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          2 * dyadicHodgeGlobalProductFace scale 2 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          4 * dyadicHodgeGlobalProductFace scale 1 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          2 * dyadicHodgeGlobalProductFace scale 0 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          dyadicHodgeGlobalProductFace scale 2 0 component coordinate input
            firstIndex secondIndex thirdIndex +
          2 * dyadicHodgeGlobalProductFace scale 1 0 component coordinate input
            firstIndex secondIndex thirdIndex +
          dyadicHodgeGlobalProductFace scale 0 0 component coordinate input
            firstIndex secondIndex thirdIndex =
        dyadicHodgeGlobalProductFace scale 2 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          (2 * dyadicHodgeGlobalProductFace scale 1 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          (dyadicHodgeGlobalProductFace scale 0 2 component coordinate input
            firstIndex secondIndex thirdIndex +
          (2 * dyadicHodgeGlobalProductFace scale 2 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          (4 * dyadicHodgeGlobalProductFace scale 1 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          (2 * dyadicHodgeGlobalProductFace scale 0 1 component coordinate input
            firstIndex secondIndex thirdIndex +
          (dyadicHodgeGlobalProductFace scale 2 0 component coordinate input
            firstIndex secondIndex thirdIndex +
          (2 * dyadicHodgeGlobalProductFace scale 1 0 component coordinate input
            firstIndex secondIndex thirdIndex +
           dyadicHodgeGlobalProductFace scale 0 0 component coordinate input
            firstIndex secondIndex thirdIndex))))))) by ring]
  exact norm_add_nine_le _ _ _ _ _ _ _ _ _

theorem norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le_majorant
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hthird : thirdIndex < dyadicHodgeApertureCount scale) :
    ‖dyadicHodgeCubeSecondDifferenceFirstSecond scale component coordinate input
        firstIndex secondIndex thirdIndex‖ ≤
      dyadicHodgeGlobalLeibnizNormMajorant scale component coordinate input
        firstIndex secondIndex thirdIndex := by
  simpa [dyadicHodgeGlobalLeibnizNormMajorant, norm_mul] using
    norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le_globalFaces
      scale component coordinate input firstIndex secondIndex thirdIndex hthird

theorem sum_dyadicHodgeGlobalLeibnizNormMajorant_eq_faceMasses
    (scale : ℕ) (component coordinate input : Fin 3) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          dyadicHodgeGlobalLeibnizNormMajorant scale component coordinate input
            firstIndex secondIndex thirdIndex) =
      dyadicHodgeGlobalProductFaceMass scale 2 2 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 1 2
          component coordinate input +
        (dyadicHodgeGlobalProductFaceMass scale 0 2 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 2 1
          component coordinate input +
        (4 * dyadicHodgeGlobalProductFaceMass scale 1 1
          component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 0 1
          component coordinate input +
        (dyadicHodgeGlobalProductFaceMass scale 2 0 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 1 0
          component coordinate input +
         dyadicHodgeGlobalProductFaceMass scale 0 0
          component coordinate input))))))) := by
  simp [dyadicHodgeGlobalLeibnizNormMajorant,
    dyadicHodgeGlobalProductFaceMass, Finset.sum_add_distrib, Finset.mul_sum]

theorem dyadicHodgeGlobalProductFaceMass_zero_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 0 0 component coordinate input ≤
      32768000000000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 0 0 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_zero_zero_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_zero_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 0 1 component coordinate input ≤
      84992000000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 0 1 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_zero_one_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_zero_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 0 2 component coordinate input ≤
      499200000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 0 2 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_zero_two_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_one_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 1 0 component coordinate input ≤
      84992000000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 1 0 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_one_zero_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_one_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 1 1 component coordinate input ≤
      307200000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 1 1 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_one_one_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_one_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 1 2 component coordinate input ≤
      2688000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 1 2 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_one_two_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_two_zero_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 2 0 component coordinate input ≤
      499200000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 2 0 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_two_zero_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_two_one_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 2 1 component coordinate input ≤
      2688000 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 2 1 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_two_one_le
    scale component coordinate input hscale

theorem dyadicHodgeGlobalProductFaceMass_two_two_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeGlobalProductFaceMass scale 2 2 component coordinate input ≤
      160 / (dyadicRadius scale : ℝ) := by
  unfold dyadicHodgeGlobalProductFaceMass
  rw [sum_norm_dyadicHodgeGlobalProductFace_eq_subset
    scale 2 2 component coordinate input (by omega) (by omega)]
  exact sum_norm_dyadicHodgeSubsetProductFace_two_two_le
    scale component coordinate input hscale

/-- Explicit inverse-radius total mass of the actual zero-padded first/second-coordinate Hodge
variation.  This is the requested two-axis dyadic kernel input: all nine product faces, both
aperture flanks, and zero-crossing stencils are present in the finite sum. -/
theorem sum_norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicHodgeCubeSecondDifferenceFirstSecond scale
            component coordinate input firstIndex secondIndex thirdIndex‖) ≤
      34000000000000 / (dyadicRadius scale : ℝ) := by
  calc
    _ ≤ (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
              dyadicHodgeGlobalLeibnizNormMajorant scale
                component coordinate input firstIndex secondIndex thirdIndex) := by
        gcongr with firstIndex hfirst secondIndex hsecond thirdIndex hthird
        exact norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le_majorant
          scale component coordinate input firstIndex secondIndex thirdIndex
          (Finset.mem_range.mp hthird)
    _ = dyadicHodgeGlobalProductFaceMass scale 2 2 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 1 2
          component coordinate input +
        (dyadicHodgeGlobalProductFaceMass scale 0 2 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 2 1
          component coordinate input +
        (4 * dyadicHodgeGlobalProductFaceMass scale 1 1
          component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 0 1
          component coordinate input +
        (dyadicHodgeGlobalProductFaceMass scale 2 0 component coordinate input +
        (2 * dyadicHodgeGlobalProductFaceMass scale 1 0
          component coordinate input +
         dyadicHodgeGlobalProductFaceMass scale 0 0
          component coordinate input))))))) :=
      sum_dyadicHodgeGlobalLeibnizNormMajorant_eq_faceMasses
        scale component coordinate input
    _ ≤ 34000000000000 / (dyadicRadius scale : ℝ) := by
      have h22 := dyadicHodgeGlobalProductFaceMass_two_two_le
        scale component coordinate input hscale
      have h12 := dyadicHodgeGlobalProductFaceMass_one_two_le
        scale component coordinate input hscale
      have h02 := dyadicHodgeGlobalProductFaceMass_zero_two_le
        scale component coordinate input hscale
      have h21 := dyadicHodgeGlobalProductFaceMass_two_one_le
        scale component coordinate input hscale
      have h11 := dyadicHodgeGlobalProductFaceMass_one_one_le
        scale component coordinate input hscale
      have h01 := dyadicHodgeGlobalProductFaceMass_zero_one_le
        scale component coordinate input hscale
      have h20 := dyadicHodgeGlobalProductFaceMass_two_zero_le
        scale component coordinate input hscale
      have h10 := dyadicHodgeGlobalProductFaceMass_one_zero_le
        scale component coordinate input hscale
      have h00 := dyadicHodgeGlobalProductFaceMass_zero_zero_le
        scale component coordinate input hscale
      have hradius : 0 < (dyadicRadius scale : ℝ) := by
        exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
      have hinverse : 0 ≤ (dyadicRadius scale : ℝ)⁻¹ := by positivity
      simp only [div_eq_mul_inv] at h22 h12 h02 h21 h11 h01 h20 h10 h00 ⊢
      calc
        _ ≤ 160 * (dyadicRadius scale : ℝ)⁻¹ +
            (2 * (2688000 * (dyadicRadius scale : ℝ)⁻¹) +
            (499200000 * (dyadicRadius scale : ℝ)⁻¹ +
            (2 * (2688000 * (dyadicRadius scale : ℝ)⁻¹) +
            (4 * (307200000 * (dyadicRadius scale : ℝ)⁻¹) +
            (2 * (84992000000 * (dyadicRadius scale : ℝ)⁻¹) +
            (499200000 * (dyadicRadius scale : ℝ)⁻¹ +
            (2 * (84992000000 * (dyadicRadius scale : ℝ)⁻¹) +
             32768000000000 * (dyadicRadius scale : ℝ)⁻¹))))))) :=
          add_le_add h22
            (add_le_add (mul_le_mul_of_nonneg_left h12 (by norm_num))
            (add_le_add h02
            (add_le_add (mul_le_mul_of_nonneg_left h21 (by norm_num))
            (add_le_add (mul_le_mul_of_nonneg_left h11 (by norm_num))
            (add_le_add (mul_le_mul_of_nonneg_left h01 (by norm_num))
            (add_le_add h20
            (add_le_add (mul_le_mul_of_nonneg_left h10 (by norm_num)) h00)))))))
        _ = 33110205952160 * (dyadicRadius scale : ℝ)⁻¹ := by ring
        _ ≤ 34000000000000 * (dyadicRadius scale : ℝ)⁻¹ := by
          gcongr
          norm_num

section Audit

#print axioms dyadicHodgeCubeSecondDifferenceFirstSecond_eq_mixedForwardDifference
#print axioms sum_norm_dyadicHodgeGlobalProductFace_eq_subset
#print axioms sum_norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
