import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeProductMass
import ElementaryHolonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation

/-!
# The actual dyadic Hodge coefficient returns its twenty-seven three-axis faces

**[proved-derived]** The generic three-axis shifted Leibniz law is specialized here to the
zero-padded Navier--Stokes dyadic band coefficient.  The source coefficient is kept as the product
of its scalar band and Hodge multiplier, and its sixty-four chronological Leibniz occurrences are
condensed into the complete `3 × 3 × 3` allocation population before any norm is taken.

This owner proves the source-specific constitutive/reconstruction law.  It does not assume a bound
on any allocation face and does not identify the resulting oriented sum with its absolute mass.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation

open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
open Soma.Holonics.Millennium.NavierStokesThreeAxisScalarSubsetVariation

/-- The three-axis backward-padded lattice chart.  Each natural address `index` is transported to
the global frequency `index - radius - 2`; addresses zero and one on every axis are therefore the
two genuine left boundary residues of the second-difference receiver. -/
def dyadicHodgeThreeAxisBackwardPaddedFrequency
    (scale firstIndex secondIndex thirdIndex : ℕ) : SpatialFrequency :=
  ![(firstIndex : ℤ) - (dyadicHodgeApertureRadius scale : ℤ) - 2,
    (secondIndex : ℤ) - (dyadicHodgeApertureRadius scale : ℤ) - 2,
    (thirdIndex : ℤ) - (dyadicHodgeApertureRadius scale : ℤ) - 2]

theorem dyadicHodgeThreeAxisBackwardPaddedFrequency_first_succ
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        (firstIndex + 1) secondIndex thirdIndex =
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex + coordinateStep 0 := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      coordinateStep] <;>
    omega

theorem dyadicHodgeThreeAxisBackwardPaddedFrequency_second_succ
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex (secondIndex + 1) thirdIndex =
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex + coordinateStep 1 := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      coordinateStep] <;>
    omega

theorem dyadicHodgeThreeAxisBackwardPaddedFrequency_third_succ
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeThreeAxisBackwardPaddedFrequency scale
        firstIndex secondIndex (thirdIndex + 1) =
      dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex + coordinateStep 2 := by
  funext axis
  fin_cases axis <;>
    simp [dyadicHodgeThreeAxisBackwardPaddedFrequency,
      coordinateStep] <;>
    omega

/-- The global direct coefficient and the finite coefficient cube agree on the complete
three-axis doubly padded chart, including all six boundary flanks. -/
theorem directDyadicHodgeCoefficient_threeAxisBackwardPadded_eq_secondPrevious
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    directDyadicHodgeCoefficient scale component coordinate input
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      zeroPaddedSecondPreviousCoefficient
        (fun firstPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (fun secondPosition ↦
              zeroPaddedSecondPreviousCoefficient
                (dyadicHodgeCubeCoefficient scale component coordinate input
                  firstPosition secondPosition)
                (dyadicHodgeApertureCount scale) thirdIndex)
            (dyadicHodgeApertureCount scale) secondIndex)
        (dyadicHodgeApertureCount scale) firstIndex := by
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
    unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
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
      unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
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
        unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
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
                hthirdInside, directDyadicHodgeCoefficient,
                directDyadicScalarCoefficient, dyadicHodgeCubeCoefficient]
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
              unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
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
            unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
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
          unfold directDyadicHodgeCoefficient directDyadicScalarCoefficient
          rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houtside]
          simp [zeroPaddedSecondPreviousCoefficient, hfirstSmall,
            zeroPaddedCoefficient, hfirstInside]

/-- Second forward difference in the first global lattice coordinate is the same operation as
second forward difference in the corresponding natural padded address. -/
theorem fwdDiff_two_threeAxisBackwardPadded_first
    (coefficient : SpatialFrequency → ℂ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 0))^[2] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[2]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            current secondIndex thirdIndex)) firstIndex := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  simp_rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_first_succ]

/-- The corresponding exact address naturality in the second coordinate. -/
theorem fwdDiff_two_threeAxisBackwardPadded_second
    (coefficient : SpatialFrequency → ℂ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 1))^[2] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[2]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex current thirdIndex)) secondIndex := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  simp_rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_second_succ]

/-- The corresponding exact address naturality in the third coordinate. -/
theorem fwdDiff_two_threeAxisBackwardPadded_third
    (coefficient : SpatialFrequency → ℂ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (coordinateStep 2))^[2] coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[2]
        (fun current ↦ coefficient
          (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
            firstIndex secondIndex current)) thirdIndex := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  simp_rw [← dyadicHodgeThreeAxisBackwardPaddedFrequency_third_succ]

/-- The global `(2,2,2)` lattice operator and the nested natural-address operator are the same
chart transport on every coefficient section. -/
theorem threeAxisMixedForwardDifference_two_two_two_backwardPadded_eq_natural
    (coefficient : SpatialFrequency → ℂ)
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    threeAxisMixedForwardDifference 0 1 2 2 2 2 coefficient
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) =
      (fwdDiff (1 : ℕ))^[2]
        (fun firstPosition ↦
          (fwdDiff (1 : ℕ))^[2]
            (fun secondPosition ↦
              (fwdDiff (1 : ℕ))^[2]
                (fun thirdPosition ↦ coefficient
                  (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                    firstPosition secondPosition thirdPosition)) thirdIndex)
            secondIndex)
        firstIndex := by
  unfold threeAxisMixedForwardDifference
  rw [fwdDiff_two_threeAxisBackwardPadded_first]
  apply congrArg (fun current : ℕ → ℂ ↦ (fwdDiff (1 : ℕ))^[2] current firstIndex)
  funext firstPosition
  rw [fwdDiff_two_threeAxisBackwardPadded_second]
  apply congrArg (fun current : ℕ → ℂ ↦ (fwdDiff (1 : ℕ))^[2] current secondIndex)
  funext secondPosition
  rw [fwdDiff_two_threeAxisBackwardPadded_third]

/-- Two natural forward differences undo the two-address delay of one zero-padded coefficient
slice and return its ordinary zero-padded second difference. -/
theorem fwdDiff_two_zeroPaddedSecondPrevious_eq_secondDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    (fwdDiff (1 : ℕ))^[2]
        (zeroPaddedSecondPreviousCoefficient coefficient count) index =
      zeroPaddedSecondDifference coefficient count index := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  rw [show index + 1 + 1 = index + 2 by omega,
    zeroPaddedSecondPreviousCoefficient_add_two,
    zeroPaddedSecondPreviousCoefficient_add_one]
  simp [zeroPaddedSecondDifference_eq_three_coefficients]
  ring

/-- A second difference in a varying address commutes through a zero-padded delayed receiver in
an independent address. -/
theorem fwdDiff_two_zeroPaddedSecondPrevious_commute
    (coefficient : ℕ → ℕ → ℂ) (count outerIndex innerIndex : ℕ) :
    (fwdDiff (1 : ℕ))^[2]
        (fun innerPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (fun outerPosition ↦ coefficient outerPosition innerPosition)
            count outerIndex) innerIndex =
      zeroPaddedSecondPreviousCoefficient
        (fun outerPosition ↦
          (fwdDiff (1 : ℕ))^[2] (coefficient outerPosition) innerIndex)
        count outerIndex := by
  unfold zeroPaddedSecondPreviousCoefficient
  split_ifs
  · simp [fwdDiff]
  · unfold zeroPaddedCoefficient
    split_ifs
    · simp [fwdDiff]
    · simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
      ring

/-- The complete triple delayed zero extension of a finite coefficient cube. -/
def threeAxisSecondPreviousCube
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondPreviousCoefficient
    (fun firstPosition ↦
      zeroPaddedSecondPreviousCoefficient
        (fun secondPosition ↦
          zeroPaddedSecondPreviousCoefficient
            (coefficient firstPosition secondPosition) count thirdIndex)
        count secondIndex)
    count firstIndex

/-- Applying two natural differences in all three addresses to the delayed cube returns the
ordered three-coordinate zero-padded second-difference cube. -/
theorem naturalThreeAxisSecondDifference_secondPreviousCube_eq
    (coefficient : ℕ → ℕ → ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    (fwdDiff (1 : ℕ))^[2]
        (fun firstPosition ↦
          (fwdDiff (1 : ℕ))^[2]
            (fun secondPosition ↦
              (fwdDiff (1 : ℕ))^[2]
                (fun thirdPosition ↦ threeAxisSecondPreviousCube coefficient count
                  firstPosition secondPosition thirdPosition) thirdIndex)
            secondIndex)
        firstIndex =
      zeroPaddedSecondDifferenceAll coefficient count count count
        firstIndex secondIndex thirdIndex := by
  unfold threeAxisSecondPreviousCube
  simp_rw [fwdDiff_two_zeroPaddedSecondPrevious_commute]
  simp_rw [fwdDiff_two_zeroPaddedSecondPrevious_eq_secondDifference]
  unfold zeroPaddedSecondDifferenceAll zeroPaddedSecondDifferenceFirst
    zeroPaddedSecondDifferenceSecond zeroPaddedSecondDifferenceThird
  rfl

/-- The actual ordered all-axis zero-padded receiver is exactly the global three-axis mixed
forward difference on the complete padded frequency chart.  This closes the chart-transition
square by composing the three one-axis naturality laws rather than expanding twenty-seven terms. -/
theorem dyadicHodgeCubeSecondDifferenceAll_eq_threeAxisMixedForwardDifference
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeCubeSecondDifferenceAll scale component coordinate input
        firstIndex secondIndex thirdIndex =
      threeAxisMixedForwardDifference 0 1 2 2 2 2
        (directDyadicHodgeCoefficient scale component coordinate input)
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) := by
  rw [threeAxisMixedForwardDifference_two_two_two_backwardPadded_eq_natural]
  unfold dyadicHodgeCubeSecondDifferenceAll
  rw [← naturalThreeAxisSecondDifference_secondPreviousCube_eq
    (dyadicHodgeCubeCoefficient scale component coordinate input)
    (dyadicHodgeApertureCount scale)]
  apply congrArg (fun current : ℕ → ℂ ↦ (fwdDiff (1 : ℕ))^[2] current firstIndex)
  funext firstPosition
  apply congrArg (fun current : ℕ → ℂ ↦ (fwdDiff (1 : ℕ))^[2] current secondIndex)
  funext secondPosition
  apply congrArg (fun current : ℕ → ℂ ↦ (fwdDiff (1 : ℕ))^[2] current thirdIndex)
  funext thirdPosition
  exact (directDyadicHodgeCoefficient_threeAxisBackwardPadded_eq_secondPrevious
    scale component coordinate input firstPosition secondPosition thirdPosition).symm

/-- One source-specific allocation face of the direct dyadic Hodge coefficient. -/
def directDyadicHodgeThreeAxisAllocationFace
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (frequency : SpatialFrequency) : ℂ :=
  threeAxisHodgeAllocationFace firstAllocation secondAllocation thirdAllocation
    (directDyadicScalarCoefficient scale)
    (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
    frequency

/-- The exact twenty-seven-face return of the direct dyadic Hodge coefficient. -/
def directDyadicHodgeThreeAxisAllocationReturn
    (scale : ℕ) (component coordinate input : Fin 3)
    (frequency : SpatialFrequency) : ℂ :=
  threeAxisHodgeAllocationReturn
    (directDyadicScalarCoefficient scale)
    (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
    frequency

/-- The actual direct coefficient reconstructs exactly from all twenty-seven allocation faces.
This is the source-specific `64 -> 27` constitutive return; no coefficient face has been omitted. -/
theorem threeAxisMixedForwardDifference_directDyadicHodgeCoefficient_eq_allocationReturn
    (scale : ℕ) (component coordinate input : Fin 3)
    (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 2 2 2
        (directDyadicHodgeCoefficient scale component coordinate input) frequency =
      directDyadicHodgeThreeAxisAllocationReturn
        scale component coordinate input frequency := by
  rw [show directDyadicHodgeCoefficient scale component coordinate input =
      fun current ↦ directDyadicScalarCoefficient scale current *
        hodgeJacobianMultiplierEntry current component coordinate input by rfl,
    threeAxisMixedForwardDifference_two_two_two_mul_eq_allocationReturn]
  rfl

/-- The actual full-coordinate zero-padded coefficient is exactly its twenty-seven-face
allocation return at the addressed padded frequency. -/
theorem dyadicHodgeCubeSecondDifferenceAll_eq_allocationReturn
    (scale : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    dyadicHodgeCubeSecondDifferenceAll scale component coordinate input
        firstIndex secondIndex thirdIndex =
      directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input
        (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
          firstIndex secondIndex thirdIndex) := by
  rw [dyadicHodgeCubeSecondDifferenceAll_eq_threeAxisMixedForwardDifference,
    threeAxisMixedForwardDifference_directDyadicHodgeCoefficient_eq_allocationReturn]

/-- The source-specific allocation address population has cardinality twenty-seven. -/
theorem directDyadicHodgeThreeAxisAllocation_address_card :
    Fintype.card (Fin 3 × Fin 3 × Fin 3) = 27 := by
  norm_num

/-- The full Boolean coordinate face is exactly the already founded ordered all-axis
zero-padded second difference. -/
theorem dyadicHodgeCubeSubsetDifference_univ_eq_all
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeCubeSubsetDifference (Finset.univ : CoordinateFace 3)
        scale component coordinate input =
      dyadicHodgeCubeSecondDifferenceAll scale component coordinate input := by
  rfl

/-- The official full-coordinate subset-mass receiver is the complete absolute population of the
ordered all-axis zero-padded coefficient difference. -/
theorem dyadicHodgeSubsetMass_univ_eq_allAxisMass
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicHodgeCubeSecondDifferenceAll scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference_univ_eq_all]

/-- The official full-coordinate mass receiver is exactly the finite norm population of the
twenty-seven-face allocation return.  This is the complete source-specific passage from the local
Leibniz occurrences to one of the eight official subset receivers. -/
theorem dyadicHodgeSubsetMass_univ_eq_allocationReturnMass
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖directDyadicHodgeThreeAxisAllocationReturn scale component coordinate input
              (dyadicHodgeThreeAxisBackwardPaddedFrequency scale
                firstIndex secondIndex thirdIndex)‖ := by
  rw [dyadicHodgeSubsetMass_univ_eq_allAxisMass]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirstIndex
  apply Finset.sum_congr rfl
  intro secondIndex _hsecondIndex
  apply Finset.sum_congr rfl
  intro thirdIndex _hthirdIndex
  rw [dyadicHodgeCubeSecondDifferenceAll_eq_allocationReturn]

section Audit

#print axioms threeAxisMixedForwardDifference_directDyadicHodgeCoefficient_eq_allocationReturn
#print axioms directDyadicHodgeThreeAxisAllocation_address_card
#print axioms directDyadicHodgeCoefficient_threeAxisBackwardPadded_eq_secondPrevious
#print axioms dyadicHodgeCubeSecondDifferenceAll_eq_threeAxisMixedForwardDifference
#print axioms dyadicHodgeCubeSecondDifferenceAll_eq_allocationReturn
#print axioms dyadicHodgeCubeSubsetDifference_univ_eq_all
#print axioms dyadicHodgeSubsetMass_univ_eq_allAxisMass
#print axioms dyadicHodgeSubsetMass_univ_eq_allocationReturnMass

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
