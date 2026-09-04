import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeMixedFubini

/-!
# Actual annular Hodge mixed variation

**[proved-derived]** This owner identifies the genuine centered three-dimensional annular Hodge
coefficient cube with the generic zero-padded mixed-Fubini population.  It transports the closed
one-line reciprocal-scale estimate to a complete one-coordinate subset law and retains exact
inner-plateau cancellation for distinct-coordinate mixed stencils.

The construction does not postulate a mixed rational estimate.  Two- and three-coordinate bounds
are advanced only through identities and estimates derived from the actual coefficient cube.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeStencilSum
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini

/-! ## Exact actual-cube reindexing -/

/-- Every displayed aperture index lies in the genuine adjacent outer cube. -/
theorem adjacentApertureFrequency_mem_outer_of_indices
    (radius firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : firstIndex < 4 * radius + 7)
    (hsecond : secondIndex < 4 * radius + 7)
    (hthird : thirdIndex < 4 * radius + 7) :
    adjacentApertureFrequency radius firstIndex secondIndex thirdIndex ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)) := by
  rw [mem_frequencyCube_iff]
  intro axis
  have hcount : centeredFrequencyCount (valleePoussinOuterRadius (radius + 1)) =
      4 * radius + 7 := centeredFrequencyCount_adjacentOuterRadius radius
  fin_cases axis
  · simpa [adjacentApertureFrequency] using
      centeredFrequency_mem_interval (valleePoussinOuterRadius (radius + 1))
        firstIndex (by simpa [hcount] using hfirst)
  · simpa [adjacentApertureFrequency] using
      centeredFrequency_mem_interval (valleePoussinOuterRadius (radius + 1))
        secondIndex (by simpa [hcount] using hsecond)
  · simpa [adjacentApertureFrequency] using
      centeredFrequency_mem_interval (valleePoussinOuterRadius (radius + 1))
        thirdIndex (by simpa [hcount] using hthird)

/-- A first-coordinate slice of the actual cube is exactly the completed one-line coefficient
chart. -/
theorem annularHodgeCoefficientSlice_first_eq_cube
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    annularHodgeCoefficientSlice radius 0
        (adjacentApertureFrequency radius 0 secondIndex thirdIndex)
        component coordinate input firstIndex =
      annularHodgeCubeCoefficient radius component coordinate input
        firstIndex secondIndex thirdIndex := by
  rw [annularHodgeCubeCoefficient_eq_actual]
  unfold annularHodgeCoefficientSlice
  dsimp only
  have hfrequency :
      replaceFrequencyCoordinate 0
          (adjacentApertureFrequency radius 0 secondIndex thirdIndex)
          (centeredFrequency (valleePoussinOuterRadius (radius + 1)) firstIndex) =
        adjacentApertureFrequency radius firstIndex secondIndex thirdIndex := by
    funext axis
    fin_cases axis <;>
      simp [adjacentApertureFrequency, replaceFrequencyCoordinate]
  rw [hfrequency]

/-- A second-coordinate slice is the same actual cube after changing the second displayed
index. -/
theorem annularHodgeCoefficientSlice_second_eq_cube
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    annularHodgeCoefficientSlice radius 1
        (adjacentApertureFrequency radius firstIndex 0 thirdIndex)
        component coordinate input secondIndex =
      annularHodgeCubeCoefficient radius component coordinate input
        firstIndex secondIndex thirdIndex := by
  rw [annularHodgeCubeCoefficient_eq_actual]
  unfold annularHodgeCoefficientSlice
  dsimp only
  have hfrequency :
      replaceFrequencyCoordinate 1
          (adjacentApertureFrequency radius firstIndex 0 thirdIndex)
          (centeredFrequency (valleePoussinOuterRadius (radius + 1)) secondIndex) =
        adjacentApertureFrequency radius firstIndex secondIndex thirdIndex := by
    funext axis
    fin_cases axis <;>
      simp [adjacentApertureFrequency, replaceFrequencyCoordinate]
  rw [hfrequency]

/-- A third-coordinate slice is the same actual cube after changing the third displayed index. -/
theorem annularHodgeCoefficientSlice_third_eq_cube
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    annularHodgeCoefficientSlice radius 2
        (adjacentApertureFrequency radius firstIndex secondIndex 0)
        component coordinate input thirdIndex =
      annularHodgeCubeCoefficient radius component coordinate input
        firstIndex secondIndex thirdIndex := by
  rw [annularHodgeCubeCoefficient_eq_actual]
  unfold annularHodgeCoefficientSlice
  dsimp only
  have hfrequency :
      replaceFrequencyCoordinate 2
          (adjacentApertureFrequency radius firstIndex secondIndex 0)
          (centeredFrequency (valleePoussinOuterRadius (radius + 1)) thirdIndex) =
        adjacentApertureFrequency radius firstIndex secondIndex thirdIndex := by
    funext axis
    fin_cases axis <;>
      simp [adjacentApertureFrequency, replaceFrequencyCoordinate]
  rw [hfrequency]

/-! ## Actual subset receivers -/

/-- First-coordinate second difference of the actual annular Hodge cube. -/
def annularHodgeCubeSecondDifferenceFirst
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceFirst
    (annularHodgeCubeCoefficient radius component coordinate input)
    (4 * radius + 7) firstIndex secondIndex thirdIndex

/-- Second differences in the first and second displayed coordinates. -/
def annularHodgeCubeSecondDifferenceFirstSecond
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedMixedSecondDifference
    (fun firstPosition secondPosition ↦
      annularHodgeCubeCoefficient radius component coordinate input
        firstPosition secondPosition thirdIndex)
    (4 * radius + 7) (4 * radius + 7) firstIndex secondIndex

/-- Second differences in all three displayed coordinates. -/
def annularHodgeCubeSecondDifferenceAll
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifferenceAll
    (annularHodgeCubeCoefficient radius component coordinate input)
    (4 * radius + 7) (4 * radius + 7) (4 * radius + 7)
    firstIndex secondIndex thirdIndex

/-- The first-coordinate actual receiver is exactly the zero-padded second difference of the
completed slice chart. -/
theorem annularHodgeCubeSecondDifferenceFirst_eq_slice
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    annularHodgeCubeSecondDifferenceFirst radius component coordinate input
        firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius 0
          (adjacentApertureFrequency radius 0 secondIndex thirdIndex)
          component coordinate input)
        (4 * radius + 7) firstIndex := by
  unfold annularHodgeCubeSecondDifferenceFirst zeroPaddedSecondDifferenceFirst
  congr 1
  funext position
  exact (annularHodgeCoefficientSlice_first_eq_cube
    radius component coordinate input position secondIndex thirdIndex).symm

/-- Complete one-coordinate subset variation of the actual cube.  The two untouched coordinates
retain their exact aperture populations; the active coordinate costs only one reciprocal scale. -/
theorem sum_norm_annularHodgeCubeSecondDifferenceFirst_le
    (radius : ℕ) (component coordinate input : Fin 3) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖annularHodgeCubeSecondDifferenceFirst radius component coordinate input
            firstIndex secondIndex thirdIndex‖) ≤
      (1937 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) ^ 2 := by
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖annularHodgeCubeSecondDifferenceFirst radius component coordinate input
            firstIndex secondIndex thirdIndex‖) =
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ∑ firstIndex ∈ Finset.range (4 * radius + 9),
            ‖annularHodgeCubeSecondDifferenceFirst radius component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro secondIndex _hsecondIndex
        rw [Finset.sum_comm]
    _ ≤
      ∑ _secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ _thirdIndex ∈ Finset.range (4 * radius + 7),
          1937 / (radius + 1 : ℝ) := by
        apply Finset.sum_le_sum
        intro secondIndex hsecondIndex
        rw [Finset.mem_range] at hsecondIndex
        apply Finset.sum_le_sum
        intro thirdIndex hthirdIndex
        rw [Finset.mem_range] at hthirdIndex
        simp_rw [annularHodgeCubeSecondDifferenceFirst_eq_slice]
        exact sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1937
          radius 0 (adjacentApertureFrequency radius 0 secondIndex thirdIndex)
            component coordinate input
            (adjacentApertureFrequency_mem_outer_of_indices radius 0 secondIndex thirdIndex
              (by omega) hsecondIndex hthirdIndex)
    _ = (1937 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) ^ 2 := by
      simp
      ring

/-! ## Exact plateau and aperture residues -/

/-- A zero-padded second difference is identically zero after its two declared terminal
stencils. -/
theorem zeroPaddedSecondDifference_eq_zero_of_count_add_two_le
    (coefficient : ℕ → ℂ) (count index : ℕ) (hindex : count + 2 ≤ index) :
    zeroPaddedSecondDifference coefficient count index = 0 := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients]
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    zeroPaddedSecondPreviousCoefficient,
    show ¬index < count by omega, show index ≠ 0 by omega,
    show ¬index - 1 < count by omega, show ¬index < 2 by omega,
    show ¬index - 2 < count by omega]

/-- A second-coordinate stencil wholly in the inner cube vanishes, including any stencil crossing
the totalized zero frequency. -/
theorem secondCoordinateSecondDifference_eq_zero_of_inner_stencil
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : radius + 2 ≤ firstIndex ∧ firstIndex ≤ 3 * radius + 4)
    (hsecondLower : radius + 4 ≤ secondIndex)
    (hsecondUpper : secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    zeroPaddedSecondDifference
        (fun position ↦ annularHodgeCubeCoefficient radius component coordinate input
          firstIndex position thirdIndex)
        (4 * radius + 7) secondIndex = 0 := by
  rw [zeroPadded_secondDifference_eq_internal _ _ secondIndex (by omega) (by omega),
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds
      radius component coordinate input firstIndex secondIndex thirdIndex hfirst
        ⟨by omega, hsecondUpper⟩ hthird,
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds
      radius component coordinate input firstIndex (secondIndex - 1) thirdIndex hfirst
        ⟨by omega, by omega⟩ hthird,
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds
      radius component coordinate input firstIndex (secondIndex - 2) thirdIndex hfirst
        ⟨by omega, by omega⟩ hthird]
  ring

/-- Every distinct first/second mixed stencil whose full `3 × 3` block lies in the inner cube
vanishes exactly.  This is the mixed zero-crossing receipt: the Hodge ratio is never evaluated as
an analytic surrogate at the origin because the actual annular coefficient is already zero. -/
theorem annularHodgeCubeSecondDifferenceFirstSecond_eq_zero_of_inner_stencil
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstLower : radius + 4 ≤ firstIndex)
    (hfirstUpper : firstIndex ≤ 3 * radius + 4)
    (hsecondLower : radius + 4 ≤ secondIndex)
    (hsecondUpper : secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    annularHodgeCubeSecondDifferenceFirstSecond radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold annularHodgeCubeSecondDifferenceFirstSecond zeroPaddedMixedSecondDifference
  rw [zeroPadded_secondDifference_eq_internal _ _ firstIndex (by omega) (by omega),
    secondCoordinateSecondDifference_eq_zero_of_inner_stencil
      radius component coordinate input firstIndex secondIndex thirdIndex
        ⟨by omega, hfirstUpper⟩ hsecondLower hsecondUpper hthird,
    secondCoordinateSecondDifference_eq_zero_of_inner_stencil
      radius component coordinate input (firstIndex - 1) secondIndex thirdIndex
        ⟨by omega, by omega⟩ hsecondLower hsecondUpper hthird,
    secondCoordinateSecondDifference_eq_zero_of_inner_stencil
      radius component coordinate input (firstIndex - 2) secondIndex thirdIndex
        ⟨by omega, by omega⟩ hsecondLower hsecondUpper hthird]
  ring

/-- No first-coordinate second-difference residue exists beyond the two exact aperture stencils. -/
theorem annularHodgeCubeSecondDifferenceFirst_eq_zero_of_aperture
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : 4 * radius + 9 ≤ firstIndex) :
    annularHodgeCubeSecondDifferenceFirst radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold annularHodgeCubeSecondDifferenceFirst zeroPaddedSecondDifferenceFirst
  exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)

/-- No two-coordinate mixed residue exists when either active index lies beyond its exact two
aperture stencils. -/
theorem annularHodgeCubeSecondDifferenceFirstSecond_eq_zero_of_aperture
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (haperture : 4 * radius + 9 ≤ firstIndex ∨ 4 * radius + 9 ≤ secondIndex) :
    annularHodgeCubeSecondDifferenceFirstSecond radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold annularHodgeCubeSecondDifferenceFirstSecond zeroPaddedMixedSecondDifference
  rcases haperture with hfirst | hsecond
  · exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)
  · have hinner : (fun firstPosition ↦ zeroPaddedSecondDifference
        (fun secondPosition ↦
          annularHodgeCubeCoefficient radius component coordinate input
            firstPosition secondPosition thirdIndex)
        (4 * radius + 7) secondIndex) = 0 := by
      funext firstPosition
      exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)
    rw [hinner]
    simp [zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
      zeroPaddedCoefficient]

/-- Specialized exact three-coordinate Abel/Fubini passage for the genuine annular Hodge cube. -/
theorem finiteCharacterSynthesisThree_annularHodge_secondDifferenceAll
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstCharacter secondCharacter thirdCharacter : ℂ) :
    finiteCharacterSynthesisThree
        (annularHodgeCubeSecondDifferenceAll radius component coordinate input)
        firstCharacter secondCharacter thirdCharacter
        (4 * radius + 9) (4 * radius + 9) (4 * radius + 9) =
      (1 - firstCharacter) ^ 2 * (1 - secondCharacter) ^ 2 *
        (1 - thirdCharacter) ^ 2 *
          finiteCharacterSynthesisThree
            (annularHodgeCubeCoefficient radius component coordinate input)
            firstCharacter secondCharacter thirdCharacter
            (4 * radius + 7) (4 * radius + 7) (4 * radius + 7) := by
  exact finiteCharacterSynthesisThree_secondDifferenceAll
    (annularHodgeCubeCoefficient radius component coordinate input)
    firstCharacter secondCharacter thirdCharacter
    (4 * radius + 7) (4 * radius + 7) (4 * radius + 7)

/-- A first-coordinate second difference commutes with zero extension in the second coordinate. -/
theorem zeroPaddedSecondDifference_zeroPaddedCoefficient_comm
    (coefficient : ℕ → ℕ → ℂ)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    zeroPaddedSecondDifference
        (fun firstPosition ↦
          zeroPaddedCoefficient (coefficient firstPosition) secondCount secondIndex)
        firstCount firstIndex =
      zeroPaddedCoefficient
        (fun secondPosition ↦ zeroPaddedSecondDifference
          (fun firstPosition ↦ coefficient firstPosition secondPosition)
          firstCount firstIndex)
        secondCount secondIndex := by
  simp only [zeroPaddedCoefficient]
  split_ifs with hinterior
  · rfl
  · simp [zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
      zeroPaddedCoefficient]

/-- The same commutation one position behind the second-coordinate stencil. -/
theorem zeroPaddedSecondDifference_zeroPaddedPreviousCoefficient_comm
    (coefficient : ℕ → ℕ → ℂ)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    zeroPaddedSecondDifference
        (fun firstPosition ↦
          zeroPaddedPreviousCoefficient (coefficient firstPosition)
            secondCount secondIndex)
        firstCount firstIndex =
      zeroPaddedPreviousCoefficient
        (fun secondPosition ↦ zeroPaddedSecondDifference
          (fun firstPosition ↦ coefficient firstPosition secondPosition)
          firstCount firstIndex)
        secondCount secondIndex := by
  unfold zeroPaddedPreviousCoefficient
  by_cases hzero : secondIndex = 0
  · simp [hzero, zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
      zeroPaddedCoefficient]
  · simp only [hzero, if_false]
    exact zeroPaddedSecondDifference_zeroPaddedCoefficient_comm
      coefficient firstCount secondCount firstIndex (secondIndex - 1)

/-- The same commutation two positions behind the second-coordinate stencil. -/
theorem zeroPaddedSecondDifference_zeroPaddedSecondPreviousCoefficient_comm
    (coefficient : ℕ → ℕ → ℂ)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    zeroPaddedSecondDifference
        (fun firstPosition ↦
          zeroPaddedSecondPreviousCoefficient (coefficient firstPosition)
            secondCount secondIndex)
        firstCount firstIndex =
      zeroPaddedSecondPreviousCoefficient
        (fun secondPosition ↦ zeroPaddedSecondDifference
          (fun firstPosition ↦ coefficient firstPosition secondPosition)
          firstCount firstIndex)
        secondCount secondIndex := by
  unfold zeroPaddedSecondPreviousCoefficient
  by_cases hsmall : secondIndex < 2
  · simp [hsmall, zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
      zeroPaddedCoefficient]
  · simp only [hsmall, if_false]
    exact zeroPaddedSecondDifference_zeroPaddedCoefficient_comm
      coefficient firstCount secondCount firstIndex (secondIndex - 2)

/-- Distinct-coordinate zero-padded second differences commute, including all four aperture
edges and corners. -/
theorem zeroPaddedMixedSecondDifference_comm
    (coefficient : ℕ → ℕ → ℂ)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    zeroPaddedMixedSecondDifference coefficient
        firstCount secondCount firstIndex secondIndex =
      zeroPaddedMixedSecondDifference
        (fun secondPosition firstPosition ↦ coefficient firstPosition secondPosition)
        secondCount firstCount secondIndex firstIndex := by
  unfold zeroPaddedMixedSecondDifference
  have hinner :
      (fun firstPosition ↦ zeroPaddedSecondDifference
        (coefficient firstPosition) secondCount secondIndex) =
      fun firstPosition ↦
        zeroPaddedCoefficient (coefficient firstPosition) secondCount secondIndex -
          2 * zeroPaddedPreviousCoefficient (coefficient firstPosition)
            secondCount secondIndex +
          zeroPaddedSecondPreviousCoefficient (coefficient firstPosition)
            secondCount secondIndex := by
    funext firstPosition
    exact zeroPaddedSecondDifference_eq_three_coefficients _ _ _
  rw [hinner, zeroPaddedSecondDifference_add, zeroPaddedSecondDifference_sub,
    zeroPaddedSecondDifference_mul_left,
    zeroPaddedSecondDifference_zeroPaddedCoefficient_comm,
    zeroPaddedSecondDifference_zeroPaddedPreviousCoefficient_comm,
    zeroPaddedSecondDifference_zeroPaddedSecondPreviousCoefficient_comm,
    zeroPaddedSecondDifference_eq_three_coefficients]

/-! ## Exact cube-to-physical-kernel transport -/

/-- A three-dimensional frequency cube is exactly the nested product of its three coordinate
intervals. -/
theorem sum_frequencyCube_eq_sum_coordinateIntervals
    {M : Type*} [AddCommMonoid M]
    (radius : ℕ) (f : SpatialFrequency → M) :
    (∑ frequency ∈ frequencyCube radius, f frequency) =
      ∑ first ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
        ∑ second ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
          ∑ third ∈ Finset.Icc (-(radius : ℤ)) (radius : ℤ),
            f ![first, second, third] := by
  classical
  let interval := Finset.Icc (-(radius : ℤ)) (radius : ℤ)
  have hproduct :
      (∑ frequency ∈ frequencyCube radius, f frequency) =
        ∑ triple ∈ interval.product (interval.product interval),
          f ![triple.1, triple.2.1, triple.2.2] := by
    apply Finset.sum_bij
      (fun frequency _hfrequency ↦
        (frequency 0, (frequency 1, frequency 2)))
    · intro frequency hfrequency
      rw [mem_frequencyCube_iff] at hfrequency
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr (hfrequency 0), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr (hfrequency 1),
          Finset.mem_Icc.mpr (hfrequency 2)⟩⟩
    · intro first _hfirst second _hsecond heq
      have hzero : first 0 = second 0 := congrArg Prod.fst heq
      have honeTwo : (first 1, first 2) = (second 1, second 2) :=
        congrArg Prod.snd heq
      have hone : first 1 = second 1 := congrArg Prod.fst honeTwo
      have htwo : first 2 = second 2 := congrArg Prod.snd honeTwo
      funext axis
      fin_cases axis <;> assumption
    · intro triple htriple
      refine ⟨![triple.1, triple.2.1, triple.2.2], ?_, ?_⟩
      · rw [mem_frequencyCube_iff]
        intro axis
        have htriple' := Finset.mem_product.mp htriple
        fin_cases axis
        · exact Finset.mem_Icc.mp htriple'.1
        · exact Finset.mem_Icc.mp (Finset.mem_product.mp htriple'.2).1
        · exact Finset.mem_Icc.mp (Finset.mem_product.mp htriple'.2).2
      · simp
    · intro frequency _hfrequency
      congr 1
      funext axis
      fin_cases axis <;> rfl
  rw [hproduct]
  simp [interval, Finset.sum_product]

/-- The centered natural chart enumerates the complete genuine three-dimensional frequency cube
without duplication. -/
theorem sum_frequencyCube_eq_sum_centeredAperture
    {M : Type*} [AddCommMonoid M]
    (radius : ℕ) (f : SpatialFrequency → M) :
    (∑ frequency ∈ frequencyCube radius, f frequency) =
      ∑ firstIndex ∈ Finset.range (centeredFrequencyCount radius),
        ∑ secondIndex ∈ Finset.range (centeredFrequencyCount radius),
          ∑ thirdIndex ∈ Finset.range (centeredFrequencyCount radius),
            f ![centeredFrequency radius firstIndex,
              centeredFrequency radius secondIndex,
              centeredFrequency radius thirdIndex] := by
  rw [sum_frequencyCube_eq_sum_coordinateIntervals]
  exact sum_Icc_sum_Icc_sum_Icc_eq_sum_centeredFrequency radius
    (fun first second third ↦ f ![first, second, third])

/-- A centered scalar character is its left endpoint phase times the natural power of the unit
character. -/
theorem fourier_centeredFrequency_eq_endpoint_mul_pow
    (radius index : ℕ) (q : UnitAddCircle) :
    fourier (centeredFrequency radius index) q =
      fourier (-(radius : ℤ)) q * fourier 1 q ^ index := by
  have hnatural : fourier (index : ℤ) q = fourier 1 q ^ index := by
    induction index with
    | zero => simp
    | succ index hinduction =>
        rw [Nat.cast_succ, fourier_add, hinduction, pow_succ]
  rw [centeredFrequency]
  have hdecomposition : (index : ℤ) - (radius : ℤ) =
      -(radius : ℤ) + (index : ℤ) := by ring
  rw [hdecomposition, fourier_add, hnatural]

/-- Common left-endpoint frequency of the centered adjacent aperture. -/
def adjacentApertureBaseFrequency (radius : ℕ) : SpatialFrequency :=
  fun _ ↦ -(valleePoussinOuterRadius (radius + 1) : ℤ)

/-- The torus character at a displayed aperture frequency is the common endpoint phase times
the three coordinate unit-character powers. -/
theorem mFourier_adjacentApertureFrequency
    (radius firstIndex secondIndex thirdIndex : ℕ)
    (q : UnitAddTorus (Fin 3)) :
    UnitAddTorus.mFourier
        (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex) q =
      UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
        fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
          fourier 1 (q 2) ^ thirdIndex := by
  dsimp only [UnitAddTorus.mFourier, adjacentApertureFrequency,
    adjacentApertureBaseFrequency, ContinuousMap.coe_mk]
  simp only [Fin.prod_univ_three]
  change
    fourier (centeredFrequency (valleePoussinOuterRadius (radius + 1)) firstIndex)
          (q 0) *
        fourier (centeredFrequency (valleePoussinOuterRadius (radius + 1)) secondIndex)
          (q 1) *
          fourier (centeredFrequency (valleePoussinOuterRadius (radius + 1)) thirdIndex)
            (q 2) =
      (fourier (-(valleePoussinOuterRadius (radius + 1) : ℤ)) (q 0) *
        fourier (-(valleePoussinOuterRadius (radius + 1) : ℤ)) (q 1) *
          fourier (-(valleePoussinOuterRadius (radius + 1) : ℤ)) (q 2)) *
        fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
          fourier 1 (q 2) ^ thirdIndex
  rw [fourier_centeredFrequency_eq_endpoint_mul_pow,
    fourier_centeredFrequency_eq_endpoint_mul_pow,
    fourier_centeredFrequency_eq_endpoint_mul_pow]
  ring

/-- **Exact physical reindexing.** Every scalar entry of the genuine adjacent Hodge kernel is the
centered cube synthesis, up to its norm-one common endpoint phase. -/
theorem adjacentHodgeJacobianKernelEntry_eq_centeredSynthesis
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    adjacentHodgeJacobianKernelEntry radius component coordinate input q =
      UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
        finiteCharacterSynthesisThree
          (annularHodgeCubeCoefficient radius component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (4 * radius + 7) (4 * radius + 7) (4 * radius + 7) := by
  unfold adjacentHodgeJacobianKernelEntry finiteFourierSynthesis
  change (∑ frequency ∈ frequencyCube
      (valleePoussinOuterRadius (radius + 1)),
        UnitAddTorus.mFourier frequency q *
          annularHodgeMultiplierCoefficient radius frequency
            component coordinate input) = _
  rw [sum_frequencyCube_eq_sum_centeredAperture]
  simp_rw [centeredFrequencyCount_adjacentOuterRadius]
  have hfrequency : ∀ firstIndex secondIndex thirdIndex,
      ![centeredFrequency (valleePoussinOuterRadius (radius + 1)) firstIndex,
        centeredFrequency (valleePoussinOuterRadius (radius + 1)) secondIndex,
        centeredFrequency (valleePoussinOuterRadius (radius + 1)) thirdIndex] =
      adjacentApertureFrequency radius firstIndex secondIndex thirdIndex := by
    intro firstIndex secondIndex thirdIndex
    rfl
  simp_rw [hfrequency, ← annularHodgeCubeCoefficient_eq_actual,
    mFourier_adjacentApertureFrequency]
  unfold finiteCharacterSynthesisThree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro firstIndex _hfirstIndex
  calc
    (∑ secondIndex ∈ Finset.range (4 * radius + 7),
      ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
        UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
            fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
              fourier 1 (q 2) ^ thirdIndex *
                annularHodgeCubeCoefficient radius component coordinate input
                  firstIndex secondIndex thirdIndex) =
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        (UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
          fourier 1 (q 0) ^ firstIndex) *
          ((∑ thirdIndex ∈ Finset.range (4 * radius + 7),
              annularHodgeCubeCoefficient radius component coordinate input
                firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex) := by
              apply Finset.sum_congr rfl
              intro secondIndex _hsecondIndex
              calc
                (∑ thirdIndex ∈ Finset.range (4 * radius + 7),
                  UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
                      fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex *
                        fourier 1 (q 2) ^ thirdIndex *
                          annularHodgeCubeCoefficient radius component coordinate input
                            firstIndex secondIndex thirdIndex) =
                    (UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
                      fourier 1 (q 0) ^ firstIndex * fourier 1 (q 1) ^ secondIndex) *
                        (∑ thirdIndex ∈ Finset.range (4 * radius + 7),
                          annularHodgeCubeCoefficient radius component coordinate input
                            firstIndex secondIndex thirdIndex *
                              fourier 1 (q 2) ^ thirdIndex) := by
                                rw [Finset.mul_sum]
                                apply Finset.sum_congr rfl
                                intro thirdIndex _hthirdIndex
                                ring
                _ = UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
                    fourier 1 (q 0) ^ firstIndex *
                      ((∑ thirdIndex ∈ Finset.range (4 * radius + 7),
                        annularHodgeCubeCoefficient radius component coordinate input
                          firstIndex secondIndex thirdIndex *
                            fourier 1 (q 2) ^ thirdIndex) *
                          fourier 1 (q 1) ^ secondIndex) := by ring
    _ = (UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
          fourier 1 (q 0) ^ firstIndex) *
        (∑ secondIndex ∈ Finset.range (4 * radius + 7),
          ((∑ thirdIndex ∈ Finset.range (4 * radius + 7),
              annularHodgeCubeCoefficient radius component coordinate input
                firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex)) := by
              rw [Finset.mul_sum]
    _ = UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
        ((∑ secondIndex ∈ Finset.range (4 * radius + 7),
          (∑ thirdIndex ∈ Finset.range (4 * radius + 7),
            annularHodgeCubeCoefficient radius component coordinate input
              firstIndex secondIndex thirdIndex * fourier 1 (q 2) ^ thirdIndex) *
            fourier 1 (q 1) ^ secondIndex) *
          fourier 1 (q 0) ^ firstIndex) := by ring

/-- Triangle control for an exact nested character synthesis when all three characters have
unit norm. -/
theorem norm_finiteCharacterSynthesisThree_le_mass
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCharacter secondCharacter thirdCharacter : ℂ)
    (firstCount secondCount thirdCount : ℕ)
    (hfirst : ‖firstCharacter‖ = 1)
    (hsecond : ‖secondCharacter‖ = 1)
    (hthird : ‖thirdCharacter‖ = 1) :
    ‖finiteCharacterSynthesisThree coefficient
        firstCharacter secondCharacter thirdCharacter
        firstCount secondCount thirdCount‖ ≤
      ∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            ‖coefficient firstIndex secondIndex thirdIndex‖ := by
  unfold finiteCharacterSynthesisThree
  calc
    ‖∑ firstIndex ∈ Finset.range firstCount,
      (∑ secondIndex ∈ Finset.range secondCount,
        (∑ thirdIndex ∈ Finset.range thirdCount,
          coefficient firstIndex secondIndex thirdIndex *
            thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex) *
              firstCharacter ^ firstIndex‖ ≤
        ∑ firstIndex ∈ Finset.range firstCount,
          ‖(∑ secondIndex ∈ Finset.range secondCount,
            (∑ thirdIndex ∈ Finset.range thirdCount,
              coefficient firstIndex secondIndex thirdIndex *
                thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex) *
                  firstCharacter ^ firstIndex‖ := norm_sum_le _ _
    _ = ∑ firstIndex ∈ Finset.range firstCount,
          ‖∑ secondIndex ∈ Finset.range secondCount,
            (∑ thirdIndex ∈ Finset.range thirdCount,
              coefficient firstIndex secondIndex thirdIndex *
                thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex‖ := by
            apply Finset.sum_congr rfl
            intro firstIndex _hfirstIndex
            simp [hfirst]
    _ ≤ ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ‖(∑ thirdIndex ∈ Finset.range thirdCount,
              coefficient firstIndex secondIndex thirdIndex *
                thirdCharacter ^ thirdIndex) * secondCharacter ^ secondIndex‖ := by
            apply Finset.sum_le_sum
            intro firstIndex _hfirstIndex
            exact norm_sum_le _ _
    _ = ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ‖∑ thirdIndex ∈ Finset.range thirdCount,
              coefficient firstIndex secondIndex thirdIndex *
                thirdCharacter ^ thirdIndex‖ := by
            apply Finset.sum_congr rfl
            intro firstIndex _hfirstIndex
            apply Finset.sum_congr rfl
            intro secondIndex _hsecondIndex
            simp [hsecond]
    _ ≤ ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖coefficient firstIndex secondIndex thirdIndex *
                thirdCharacter ^ thirdIndex‖ := by
            apply Finset.sum_le_sum
            intro firstIndex _hfirstIndex
            apply Finset.sum_le_sum
            intro secondIndex _hsecondIndex
            exact norm_sum_le _ _
    _ = ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖coefficient firstIndex secondIndex thirdIndex‖ := by
            apply Finset.sum_congr rfl
            intro firstIndex _hfirstIndex
            apply Finset.sum_congr rfl
            intro secondIndex _hsecondIndex
            apply Finset.sum_congr rfl
            intro thirdIndex _hthirdIndex
            simp [hthird]

/-- Exact one-coordinate Abel identity for the actual physical Hodge entry kernel. -/
theorem adjacentHodgeJacobianKernelEntry_firstAbel
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 *
        adjacentHodgeJacobianKernelEntry radius component coordinate input q =
      UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
        finiteCharacterSynthesisThree
          (annularHodgeCubeSecondDifferenceFirst radius component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (4 * radius + 9) (4 * radius + 7) (4 * radius + 7) := by
  rw [adjacentHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold annularHodgeCubeSecondDifferenceFirst
  rw [finiteCharacterSynthesisThree_secondDifferenceFirst]
  ring

/-- **Explicit actual-kernel estimate.** One exact Abel factor controls every genuine physical
Hodge entry with the completed reciprocal-scale constant `1937`; no scalar middle-band envelope
is substituted. -/
theorem norm_adjacentHodgeJacobianKernelEntry_firstAbel_le
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    ‖(1 - fourier 1 (q 0)) ^ 2 *
        adjacentHodgeJacobianKernelEntry radius component coordinate input q‖ ≤
      (1937 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) ^ 2 := by
  rw [adjacentHodgeJacobianKernelEntry_firstAbel, norm_mul]
  have hbase :
      ‖UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  rw [hbase, one_mul]
  exact (norm_finiteCharacterSynthesisThree_le_mass
    (annularHodgeCubeSecondDifferenceFirst radius component coordinate input)
    (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
    (4 * radius + 9) (4 * radius + 7) (4 * radius + 7)
    (by rw [fourier_apply]; exact Circle.norm_coe _)
    (by rw [fourier_apply]; exact Circle.norm_coe _)
    (by rw [fourier_apply]; exact Circle.norm_coe _)).trans
      (sum_norm_annularHodgeCubeSecondDifferenceFirst_le
        radius component coordinate input)

/-- Away from the first-coordinate character identity, the genuine physical kernel entry has the
corresponding explicit inverse-square bound.  The excluded identity face is the retained Abel
obstruction. -/
theorem norm_adjacentHodgeJacobianKernelEntry_le_of_firstCharacter_ne_one
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3))
    (hcharacter : fourier 1 (q 0) ≠ 1) :
    ‖adjacentHodgeJacobianKernelEntry radius component coordinate input q‖ ≤
      ((1937 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) ^ 2) /
        ‖1 - fourier 1 (q 0)‖ ^ 2 := by
  have hfactor : 0 < ‖1 - fourier 1 (q 0)‖ ^ 2 := by
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hcharacter.symm))
  rw [le_div_iff₀ hfactor]
  have hweighted := norm_adjacentHodgeJacobianKernelEntry_firstAbel_le
    radius component coordinate input q
  simpa [norm_mul, norm_pow, mul_comm] using hweighted

/-- Exact triple Abel identity for the actual physical Hodge entry kernel.  All aperture and
zero-crossing residues remain in the genuine mixed coefficient population on the right. -/
theorem adjacentHodgeJacobianKernelEntry_tripleAbel
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    (1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
          (1 - fourier 1 (q 2)) ^ 2 *
            adjacentHodgeJacobianKernelEntry radius component coordinate input q =
      UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q *
        finiteCharacterSynthesisThree
          (annularHodgeCubeSecondDifferenceAll radius component coordinate input)
          (fourier 1 (q 0)) (fourier 1 (q 1)) (fourier 1 (q 2))
          (4 * radius + 9) (4 * radius + 9) (4 * radius + 9) := by
  rw [adjacentHodgeJacobianKernelEntry_eq_centeredSynthesis]
  unfold annularHodgeCubeSecondDifferenceAll
  rw [finiteCharacterSynthesisThree_secondDifferenceAll]
  ring

/-- The actual physical kernel, after the three exact Abel factors, is controlled by the genuine
three-coordinate mixed variation mass with constant one. -/
theorem norm_adjacentHodgeJacobianKernelEntry_tripleAbel_le_mixedMass
    (radius : ℕ) (component coordinate input : Fin 3)
    (q : UnitAddTorus (Fin 3)) :
    ‖(1 - fourier 1 (q 0)) ^ 2 * (1 - fourier 1 (q 1)) ^ 2 *
          (1 - fourier 1 (q 2)) ^ 2 *
            adjacentHodgeJacobianKernelEntry radius component coordinate input q‖ ≤
      ∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 9),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
            ‖annularHodgeCubeSecondDifferenceAll radius component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  rw [adjacentHodgeJacobianKernelEntry_tripleAbel, norm_mul]
  have hbase :
      ‖UnitAddTorus.mFourier (adjacentApertureBaseFrequency radius) q‖ = 1 := by
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
      fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  rw [hbase, one_mul]
  apply norm_finiteCharacterSynthesisThree_le_mass
  all_goals rw [fourier_apply]
  all_goals exact Circle.norm_coe _

/-! ## Three-coordinate boundary residues -/

/-- The ordered three-coordinate second difference equals a third-coordinate second difference
of the first/second mixed population.  This rotates the exact Fubini order without changing any
zero-padding edge or corner. -/
theorem zeroPaddedSecondDifferenceAll_rotateThird
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    zeroPaddedSecondDifferenceAll coefficient
        firstCount secondCount thirdCount firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifference
        (fun thirdPosition ↦
          zeroPaddedMixedSecondDifference
            (fun firstPosition secondPosition ↦
              coefficient firstPosition secondPosition thirdPosition)
            firstCount secondCount firstIndex secondIndex)
        thirdCount thirdIndex := by
  unfold zeroPaddedSecondDifferenceAll zeroPaddedSecondDifferenceFirst
    zeroPaddedSecondDifferenceSecond zeroPaddedSecondDifferenceThird
  have hsecondThird : ∀ firstPosition,
      (fun firstPosition' ↦ zeroPaddedSecondDifference
        (fun secondPosition ↦ zeroPaddedSecondDifference
          (coefficient firstPosition' secondPosition) thirdCount thirdIndex)
        secondCount secondIndex) firstPosition =
      (fun firstPosition' ↦ zeroPaddedSecondDifference
        (fun thirdPosition ↦ zeroPaddedSecondDifference
          (fun secondPosition ↦ coefficient firstPosition' secondPosition thirdPosition)
          secondCount secondIndex)
        thirdCount thirdIndex) firstPosition := by
    intro firstPosition
    exact zeroPaddedMixedSecondDifference_comm
      (fun secondPosition thirdPosition ↦
        coefficient firstPosition secondPosition thirdPosition)
      secondCount thirdCount secondIndex thirdIndex
  simp_rw [hsecondThird]
  exact zeroPaddedMixedSecondDifference_comm
    (fun firstPosition thirdPosition ↦
      zeroPaddedSecondDifference
        (fun secondPosition ↦ coefficient firstPosition secondPosition thirdPosition)
        secondCount secondIndex)
    firstCount thirdCount firstIndex thirdIndex

/-- Every full `3 × 3 × 3` stencil contained in the inner plateau vanishes exactly, including
the totalized zero-frequency crossing. -/
theorem annularHodgeCubeSecondDifferenceAll_eq_zero_of_inner_stencil
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstLower : radius + 4 ≤ firstIndex)
    (hfirstUpper : firstIndex ≤ 3 * radius + 4)
    (hsecondLower : radius + 4 ≤ secondIndex)
    (hsecondUpper : secondIndex ≤ 3 * radius + 4)
    (hthirdLower : radius + 4 ≤ thirdIndex)
    (hthirdUpper : thirdIndex ≤ 3 * radius + 4) :
    annularHodgeCubeSecondDifferenceAll radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold annularHodgeCubeSecondDifferenceAll
  rw [zeroPaddedSecondDifferenceAll_rotateThird]
  change zeroPaddedSecondDifference
    (fun thirdPosition ↦
      annularHodgeCubeSecondDifferenceFirstSecond radius component coordinate input
        firstIndex secondIndex thirdPosition)
    (4 * radius + 7) thirdIndex = 0
  rw [zeroPadded_secondDifference_eq_internal _ _ thirdIndex (by omega) (by omega),
    annularHodgeCubeSecondDifferenceFirstSecond_eq_zero_of_inner_stencil
      radius component coordinate input firstIndex secondIndex thirdIndex
        hfirstLower hfirstUpper hsecondLower hsecondUpper ⟨by omega, hthirdUpper⟩,
    annularHodgeCubeSecondDifferenceFirstSecond_eq_zero_of_inner_stencil
      radius component coordinate input firstIndex secondIndex (thirdIndex - 1)
        hfirstLower hfirstUpper hsecondLower hsecondUpper ⟨by omega, by omega⟩,
    annularHodgeCubeSecondDifferenceFirstSecond_eq_zero_of_inner_stencil
      radius component coordinate input firstIndex secondIndex (thirdIndex - 2)
        hfirstLower hfirstUpper hsecondLower hsecondUpper ⟨by omega, by omega⟩]
  ring

/-- The three-coordinate mixed population has no residue beyond the two exact terminal stencils
in any active coordinate. -/
theorem annularHodgeCubeSecondDifferenceAll_eq_zero_of_aperture
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (haperture : 4 * radius + 9 ≤ firstIndex ∨
      4 * radius + 9 ≤ secondIndex ∨ 4 * radius + 9 ≤ thirdIndex) :
    annularHodgeCubeSecondDifferenceAll radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  unfold annularHodgeCubeSecondDifferenceAll
  rcases haperture with hfirst | hsecond | hthird
  · unfold zeroPaddedSecondDifferenceAll zeroPaddedSecondDifferenceFirst
    exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)
  · unfold zeroPaddedSecondDifferenceAll zeroPaddedSecondDifferenceFirst
      zeroPaddedSecondDifferenceSecond
    have hinner : (fun firstPosition ↦ zeroPaddedSecondDifference
        (fun secondPosition ↦
          zeroPaddedSecondDifferenceThird
            (annularHodgeCubeCoefficient radius component coordinate input)
            (4 * radius + 7) firstPosition secondPosition thirdIndex)
        (4 * radius + 7) secondIndex) = 0 := by
      funext firstPosition
      exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)
    rw [hinner]
    simp [zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
      zeroPaddedCoefficient]
  · rw [zeroPaddedSecondDifferenceAll_rotateThird]
    exact zeroPaddedSecondDifference_eq_zero_of_count_add_two_le _ _ _ (by omega)

section Audit

#print axioms sum_frequencyCube_eq_sum_centeredAperture
#print axioms adjacentHodgeJacobianKernelEntry_eq_centeredSynthesis
#print axioms norm_adjacentHodgeJacobianKernelEntry_firstAbel_le
#print axioms norm_adjacentHodgeJacobianKernelEntry_le_of_firstCharacter_ne_one
#print axioms norm_adjacentHodgeJacobianKernelEntry_tripleAbel_le_mixedMass
#print axioms zeroPaddedMixedSecondDifference_comm
#print axioms annularHodgeCubeSecondDifferenceAll_eq_zero_of_inner_stencil
#print axioms annularHodgeCubeSecondDifferenceAll_eq_zero_of_aperture

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation
