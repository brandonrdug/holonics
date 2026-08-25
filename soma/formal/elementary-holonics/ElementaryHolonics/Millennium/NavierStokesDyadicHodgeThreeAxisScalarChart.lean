import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
import ElementaryHolonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation

/-!
# Every three-axis scalar allocation commutes with the padded lattice chart

**[proved-derived]** The direct dyadic scalar band is transported from the global lattice into
the finite coefficient cube with both boundary residues on every axis retained.  Arbitrary
admitted orders `(a,b,c) ∈ {0,1,2}³` then commute through that chart and become the corresponding
natural zero-padded tensor variation.

This is a reconstruction law for all twenty-seven scalar hands of the full Hodge Leibniz return.
It assumes no Hodge bound.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation

/-- The natural subset address whose scalar face ends at `(firstIndex, secondIndex, thirdIndex)`.
Each global address is shifted by the complement of the selected scalar order. -/
def dyadicHodgeThreeAxisSubsetPaddedFrequency
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : SpatialFrequency :=
  dyadicHodgeThreeAxisBackwardPaddedFrequency scale
    (firstIndex + (2 - firstOrder))
    (secondIndex + (2 - secondOrder))
    (thirdIndex + (2 - thirdOrder))

/-- The direct scalar band and its finite cube agree on the complete three-axis delayed chart. -/
theorem directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_secondPrevious
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicScalarCoefficient scale
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      threeAxisSecondPreviousCube (dyadicTensorBandCubeCoefficient scale)
        (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex := by
  unfold threeAxisSecondPreviousCube
  by_cases hfirstSmall : firstIndex < 2
  · have houtside :
        dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex secondIndex thirdIndex ∉
          frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
      intro hmem
      have hcoordinate :=
        (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
      simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
        dyadicHodgeApertureRadius] at hcoordinate
      omega
    unfold directDyadicScalarCoefficient
    rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
    simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall]
  · by_cases hsecondSmall : secondIndex < 2
    · have houtside :
          dyadicHodgeThreeAxisBackwardPaddedFrequency scale
              firstIndex secondIndex thirdIndex ∉
            frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
        intro hmem
        have hcoordinate :=
          (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
        simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
          dyadicHodgeApertureRadius] at hcoordinate
        omega
      unfold directDyadicScalarCoefficient
      rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
      simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
        zeroPaddedCoefficient]
    · by_cases hthirdSmall : thirdIndex < 2
      · have houtside :
            dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                firstIndex secondIndex thirdIndex ∉
              frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
          intro hmem
          have hcoordinate :=
            (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 2
          simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
            dyadicHodgeApertureRadius] at hcoordinate
          omega
        unfold directDyadicScalarCoefficient
        rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
        simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
          hthirdSmall, zeroPaddedCoefficient]
      · by_cases hfirstInside :
          firstIndex - 2 < dyadicHodgeApertureCount scale
        · by_cases hsecondInside :
            secondIndex - 2 < dyadicHodgeApertureCount scale
          · by_cases hthirdInside :
              thirdIndex - 2 < dyadicHodgeApertureCount scale
            · have hfrequency :
                  dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                      firstIndex secondIndex thirdIndex =
                    dyadicHodgeApertureFrequency scale
                      (firstIndex - 2) (secondIndex - 2) (thirdIndex - 2) := by
                funext axis
                fin_cases axis <;>
                  simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
                    dyadicHodgeApertureFrequency, centeredFrequency] <;>
                  omega
              rw [hfrequency]
              simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
                hthirdSmall, zeroPaddedCoefficient, hfirstInside, hsecondInside,
                hthirdInside, directDyadicScalarCoefficient,
                dyadicTensorBandCubeCoefficient_eq_actual]
            · have houtside :
                  dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                      firstIndex secondIndex thirdIndex ∉
                    frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
                intro hmem
                have hcoordinate :=
                  (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 2
                unfold dyadicHodgeApertureCount centeredFrequencyCount
                  dyadicHodgeApertureRadius at hthirdInside
                simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
                  dyadicHodgeApertureRadius] at hcoordinate
                omega
              unfold directDyadicScalarCoefficient
              rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
              simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
                hthirdSmall, zeroPaddedCoefficient, hfirstInside, hsecondInside,
                hthirdInside]
          · have houtside :
                dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                    firstIndex secondIndex thirdIndex ∉
                  frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
              intro hmem
              have hcoordinate :=
                (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 1
              unfold dyadicHodgeApertureCount centeredFrequencyCount
                dyadicHodgeApertureRadius at hsecondInside
              simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
                dyadicHodgeApertureRadius] at hcoordinate
              omega
            unfold directDyadicScalarCoefficient
            rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
            simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall, hsecondSmall,
              zeroPaddedCoefficient, hfirstInside, hsecondInside]
        · have houtside :
              dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                  firstIndex secondIndex thirdIndex ∉
                frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
            intro hmem
            have hcoordinate :=
              (mem_frequencyCube_iff (dyadicHodgeOuterCutoff (scale + 1)) _).mp hmem 0
            unfold dyadicHodgeApertureCount centeredFrequencyCount
              dyadicHodgeApertureRadius at hfirstInside
            simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
              dyadicHodgeApertureRadius] at hcoordinate
            omega
          unfold directDyadicScalarCoefficient
          rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
          simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall,
            zeroPaddedCoefficient, hfirstInside]

/-- Arbitrary admitted order in the first global coordinate is natural forward difference on its
address index. -/
theorem fwdDiff_iter_threeAxisBackwardPadded_first
    (coefficient : SpatialFrequency → ℂ) (order : ℕ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 0))^[order] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[order]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            current secondIndex thirdIndex)) firstIndex := by
  induction order generalizing firstIndex with
  | zero => rfl
  | succ order ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_first_succ]
      rw [ih, ih]

/-- The corresponding arbitrary-order chart naturality in the second coordinate. -/
theorem fwdDiff_iter_threeAxisBackwardPadded_second
    (coefficient : SpatialFrequency → ℂ) (order : ℕ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 1))^[order] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[order]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex current thirdIndex)) secondIndex := by
  induction order generalizing secondIndex with
  | zero => rfl
  | succ order ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_second_succ]
      rw [ih, ih]

/-- The corresponding arbitrary-order chart naturality in the third coordinate. -/
theorem fwdDiff_iter_threeAxisBackwardPadded_third
    (coefficient : SpatialFrequency → ℂ) (order : ℕ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 2))^[order] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[order]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex secondIndex current)) thirdIndex := by
  induction order generalizing thirdIndex with
  | zero => rfl
  | succ order ih =>
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_third_succ]
      rw [ih, ih]

/-- Every three-axis mixed order is transported to the same nested natural-address operator. -/
theorem threeAxisMixedForwardDifference_backwardPadded_eq_natural
    (coefficient : SpatialFrequency → ℂ)
    (firstOrder secondOrder thirdOrder : ℕ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[firstOrder]
        (fun firstPosition ↦
          (fwdDiff (1 : ℕ))^[secondOrder]
            (fun secondPosition ↦
              (fwdDiff (1 : ℕ))^[thirdOrder]
                (fun thirdPosition ↦ coefficient
                  (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                    firstPosition secondPosition thirdPosition)) thirdIndex)
            secondIndex)
        firstIndex := by
  unfold threeAxisMixedForwardDifference
  rw [fwdDiff_iter_threeAxisBackwardPadded_first]
  apply congrArg (fun current : ℕ → ℂ ↦
    (fwdDiff (1 : ℕ))^[firstOrder] current firstIndex)
  funext firstPosition
  rw [fwdDiff_iter_threeAxisBackwardPadded_second]
  apply congrArg (fun current : ℕ → ℂ ↦
    (fwdDiff (1 : ℕ))^[secondOrder] current secondIndex)
  funext secondPosition
  rw [fwdDiff_iter_threeAxisBackwardPadded_third]

/-- An admitted natural forward order cancels exactly the complementary delayed addresses. -/
theorem fwdDiff_iter_zeroPaddedSecondPrevious_shift_eq_variation
    (order : ℕ) (horder : order ≤ 2) (coefficient : ℕ → ℂ)
    (count index : ℕ) (hindex : index < count + order) :
    (fwdDiff (1 : ℕ))^[order]
        (zeroPaddedSecondPreviousCoefficient coefficient count)
        (index + (2 - order)) =
      zeroPaddedVariation order coefficient count index := by
  interval_cases order
  · have hinside : index < count := by omega
    simp [zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient,
      zeroPaddedVariation, hinside]
  · simp only [Function.iterate_one, fwdDiff,
      zeroPaddedSecondPreviousCoefficient_add_two,
      zeroPaddedSecondPreviousCoefficient_add_one,
      zeroPaddedVariation,
      zeroPaddedBackwardDifference_eq_current_sub_previous]
  · simpa [zeroPaddedVariation] using
      fwdDiff_two_zeroPaddedSecondPrevious_eq_secondDifference coefficient count index

/-- Arbitrary admitted natural differences commute through an independent delayed address. -/
theorem fwdDiff_iter_zeroPaddedSecondPrevious_commute
    (order : ℕ) (horder : order ≤ 2)
    (coefficient : ℕ → ℕ → ℂ) (count outerIndex innerIndex : ℕ) :
    (fwdDiff (1 : ℕ))^[order]
        (fun innerPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (fun outerPosition ↦ coefficient outerPosition innerPosition)
            count outerIndex) innerIndex =
      zeroPaddedSecondPreviousCoefficient
        (fun outerPosition ↦
          (fwdDiff (1 : ℕ))^[order] (coefficient outerPosition) innerIndex)
        count outerIndex := by
  interval_cases order
  · rfl
  · unfold zeroPaddedSecondPreviousCoefficient
    split_ifs
    · simp [fwdDiff]
    · unfold zeroPaddedCoefficient
      split_ifs
      · simp [fwdDiff]
      · simp only [Function.iterate_one, fwdDiff]
        ring
  · exact fwdDiff_two_zeroPaddedSecondPrevious_commute
      coefficient count outerIndex innerIndex

/-- Nested admitted natural orders turn the delayed cube into its nested zero-padded variation. -/
def threeAxisZeroPaddedVariation
    (firstOrder secondOrder thirdOrder : ℕ)
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedVariation firstOrder
    (fun firstPosition ↦
      zeroPaddedVariation secondOrder
        (fun secondPosition ↦
          zeroPaddedVariation thirdOrder
            (coefficient firstPosition secondPosition) count thirdIndex)
        count secondIndex)
    count firstIndex

theorem naturalThreeAxisDifference_secondPreviousCube_shift_eq_variation
    (firstOrder secondOrder thirdOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2)
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstIndex : firstIndex < count + firstOrder)
    (hsecondIndex : secondIndex < count + secondOrder)
    (hthirdIndex : thirdIndex < count + thirdOrder) :
    (fwdDiff (1 : ℕ))^[firstOrder]
        (fun firstPosition ↦
          (fwdDiff (1 : ℕ))^[secondOrder]
            (fun secondPosition ↦
              (fwdDiff (1 : ℕ))^[thirdOrder]
                (fun thirdPosition ↦ threeAxisSecondPreviousCube coefficient count
                  firstPosition secondPosition thirdPosition)
                (thirdIndex + (2 - thirdOrder)))
            (secondIndex + (2 - secondOrder)))
        (firstIndex + (2 - firstOrder)) =
      threeAxisZeroPaddedVariation firstOrder secondOrder thirdOrder coefficient count
        firstIndex secondIndex thirdIndex := by
  unfold threeAxisSecondPreviousCube
  simp_rw [fwdDiff_iter_zeroPaddedSecondPrevious_commute thirdOrder hthirdOrder]
  simp_rw [fwdDiff_iter_zeroPaddedSecondPrevious_shift_eq_variation thirdOrder
    hthirdOrder _ count thirdIndex hthirdIndex]
  simp_rw [fwdDiff_iter_zeroPaddedSecondPrevious_commute secondOrder hsecondOrder]
  simp_rw [fwdDiff_iter_zeroPaddedSecondPrevious_shift_eq_variation secondOrder
    hsecondOrder _ count secondIndex hsecondIndex]
  rw [fwdDiff_iter_zeroPaddedSecondPrevious_shift_eq_variation firstOrder
    hfirstOrder _ count firstIndex hfirstIndex]
  rfl

/-- Tensor separation commutes with all three admitted zero-padded orders. -/
theorem threeAxisZeroPaddedVariation_separatedTensorCoefficient
    (firstOrder secondOrder thirdOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2)
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    threeAxisZeroPaddedVariation firstOrder secondOrder thirdOrder
        (separatedTensorCoefficient first second third) count
        firstIndex secondIndex thirdIndex =
      separatedTensorCoefficient
        (fun position ↦ zeroPaddedVariation firstOrder first count position)
        (fun position ↦ zeroPaddedVariation secondOrder second count position)
        (fun position ↦ zeroPaddedVariation thirdOrder third count position)
        firstIndex secondIndex thirdIndex := by
  unfold threeAxisZeroPaddedVariation
  have hthird :
      (fun firstPosition ↦
        zeroPaddedVariation secondOrder
          (fun secondPosition ↦
            zeroPaddedVariation thirdOrder
              (fun thirdPosition ↦ separatedTensorCoefficient first second third
                firstPosition secondPosition thirdPosition)
              count thirdIndex)
          count secondIndex) =
        fun firstPosition ↦
          zeroPaddedVariation secondOrder
            (fun secondPosition ↦ separatedTensorCoefficient first second
              (fun position ↦ zeroPaddedVariation thirdOrder third count position)
              firstPosition secondPosition thirdIndex)
            count secondIndex := by
    funext firstPosition
    apply congrArg (fun coefficient : ℕ → ℂ ↦
      zeroPaddedVariation secondOrder coefficient count secondIndex)
    funext secondPosition
    have hfunction :
        (fun thirdPosition ↦ separatedTensorCoefficient first second third
          firstPosition secondPosition thirdPosition) =
          fun thirdPosition ↦ third thirdPosition *
            (first firstPosition * second secondPosition) := by
      funext thirdPosition
      simp [separatedTensorCoefficient]
      ring
    rw [hfunction, zeroPaddedVariation_mul_right thirdOrder hthirdOrder]
    unfold separatedTensorCoefficient
    ring
  rw [hthird]
  exact zeroPaddedVariation_separatedTensorCoefficient
    firstOrder secondOrder hfirstOrder hsecondOrder first second
      (fun position ↦ zeroPaddedVariation thirdOrder third count position)
      count firstIndex secondIndex thirdIndex

/-- The finite direct-band cube variation is the existing next-minus-base tensor variation. -/
theorem threeAxisZeroPaddedVariation_dyadicTensorBandCubeCoefficient_eq
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2)
    (firstIndex secondIndex thirdIndex : ℕ) :
    threeAxisZeroPaddedVariation firstOrder secondOrder thirdOrder
        (dyadicTensorBandCubeCoefficient scale) (dyadicHodgeApertureCount scale)
        firstIndex secondIndex thirdIndex =
      dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
        firstIndex secondIndex thirdIndex := by
  unfold threeAxisZeroPaddedVariation dyadicTensorBandCubeCoefficient
  have hthird :
      (fun firstPosition ↦
        zeroPaddedVariation secondOrder
          (fun secondPosition ↦
            zeroPaddedVariation thirdOrder
              (fun thirdPosition ↦
                dyadicNextTensorCubeCoefficient scale firstPosition secondPosition
                    thirdPosition -
                  dyadicBaseTensorCubeCoefficient scale firstPosition secondPosition
                    thirdPosition)
              (dyadicHodgeApertureCount scale) thirdIndex)
          (dyadicHodgeApertureCount scale) secondIndex) =
        fun firstPosition ↦
          zeroPaddedVariation secondOrder
            (fun secondPosition ↦
              zeroPaddedVariation thirdOrder
                (dyadicNextTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex -
              zeroPaddedVariation thirdOrder
                (dyadicBaseTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex := by
    funext firstPosition
    apply congrArg (fun coefficient : ℕ → ℂ ↦
      zeroPaddedVariation secondOrder coefficient
        (dyadicHodgeApertureCount scale) secondIndex)
    funext secondPosition
    exact zeroPaddedVariation_sub thirdOrder hthirdOrder _ _ _ _
  rw [hthird]
  have hsecond :
      (fun firstPosition ↦
        zeroPaddedVariation secondOrder
          (fun secondPosition ↦
            zeroPaddedVariation thirdOrder
              (dyadicNextTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex -
            zeroPaddedVariation thirdOrder
              (dyadicBaseTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex)
          (dyadicHodgeApertureCount scale) secondIndex) =
        fun firstPosition ↦
          zeroPaddedVariation secondOrder
            (fun secondPosition ↦
              zeroPaddedVariation thirdOrder
                (dyadicNextTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex -
          zeroPaddedVariation secondOrder
            (fun secondPosition ↦
              zeroPaddedVariation thirdOrder
                (dyadicBaseTensorCubeCoefficient scale firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex := by
    funext firstPosition
    exact zeroPaddedVariation_sub secondOrder hsecondOrder _ _ _ _
  rw [hsecond, zeroPaddedVariation_sub firstOrder hfirstOrder]
  rw [show dyadicNextTensorCubeCoefficient scale =
      separatedTensorCoefficient (dyadicNextCoordinateSlice scale)
        (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale) by rfl,
    show dyadicBaseTensorCubeCoefficient scale =
      separatedTensorCoefficient (dyadicBaseCoordinateSlice scale)
        (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale) by rfl]
  change
    threeAxisZeroPaddedVariation firstOrder secondOrder thirdOrder
        (separatedTensorCoefficient (dyadicNextCoordinateSlice scale)
          (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale))
        (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex -
      threeAxisZeroPaddedVariation firstOrder secondOrder thirdOrder
        (separatedTensorCoefficient (dyadicBaseCoordinateSlice scale)
          (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale))
        (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex = _
  rw [threeAxisZeroPaddedVariation_separatedTensorCoefficient
      firstOrder secondOrder thirdOrder hfirstOrder hsecondOrder hthirdOrder,
    threeAxisZeroPaddedVariation_separatedTensorCoefficient
      firstOrder secondOrder thirdOrder hfirstOrder hsecondOrder hthirdOrder]
  rfl

/-- **All twenty-seven scalar chart faces.** Every admitted global mixed scalar face at its exact
shifted padded address is the existing bounded natural tensor variation. -/
theorem threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2)
    (hfirstIndex : firstIndex < dyadicHodgeApertureCount scale + firstOrder)
    (hsecondIndex : secondIndex < dyadicHodgeApertureCount scale + secondOrder)
    (hthirdIndex : thirdIndex < dyadicHodgeApertureCount scale + thirdOrder) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
        (directDyadicScalarCoefficient scale)
        (dyadicHodgeThreeAxisSubsetPaddedFrequency scale
          firstOrder secondOrder thirdOrder firstIndex secondIndex thirdIndex) =
      dyadicTensorBandThreeAxisVariation scale firstOrder secondOrder thirdOrder
        firstIndex secondIndex thirdIndex := by
  unfold dyadicHodgeThreeAxisSubsetPaddedFrequency
  rw [threeAxisMixedForwardDifference_backwardPadded_eq_natural]
  simp_rw [directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_secondPrevious]
  rw [naturalThreeAxisDifference_secondPreviousCube_shift_eq_variation
    firstOrder secondOrder thirdOrder hfirstOrder hsecondOrder hthirdOrder
    (dyadicTensorBandCubeCoefficient scale) (dyadicHodgeApertureCount scale)
    firstIndex secondIndex thirdIndex hfirstIndex hsecondIndex hthirdIndex]
  exact threeAxisZeroPaddedVariation_dyadicTensorBandCubeCoefficient_eq
    scale firstOrder secondOrder thirdOrder hfirstOrder hsecondOrder hthirdOrder
      firstIndex secondIndex thirdIndex

section Audit

#print axioms directDyadicScalarCoefficient_threeAxisBackwardPadded_eq_secondPrevious
#print axioms threeAxisMixedForwardDifference_backwardPadded_eq_natural
#print axioms naturalThreeAxisDifference_secondPreviousCube_shift_eq_variation
#print axioms threeAxisZeroPaddedVariation_dyadicTensorBandCubeCoefficient_eq
#print axioms threeAxisMixedForwardDifference_directDyadicScalarCoefficient_subsetPadded_eq

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisScalarChart
