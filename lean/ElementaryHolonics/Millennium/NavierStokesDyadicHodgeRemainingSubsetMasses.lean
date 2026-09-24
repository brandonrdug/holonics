import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeThreeAxisFullMass
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeHaarReceiver

/-!
# Empty and first/second Boolean dyadic Hodge receivers

**[proved-derived]** The full coordinate receiver is only one member of the Boolean receiver cube.
This owner begins the exact residual closure with the two faces whose source-specific carriers are
already present: the zero-order coefficient cube and the first/second two-axis variation.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses

open Soma.Holonics.CoordinateSubsetReceiver
open Soma.Holonics.CoordinateHaarReceiver
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeTwoAxisMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSubsetReceivers
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisFullMass
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeThreeAxisAllocation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeHaarReceiver
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation

/-! ## Exact finite reconstruction from the returned difference -/

/-- A zero-padded finite coefficient is the exact prefix sum of its returned backward
differences.  This is the boundary-preserving gluing law: the omitted integration constant is fixed
by the declared zero exterior, rather than selected by an inverse. -/
theorem sum_zeroPaddedBackwardDifference_eq_zeroPaddedCoefficient
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    (∑ position ∈ Finset.range (index + 1),
        zeroPaddedBackwardDifference coefficient count position) =
      zeroPaddedCoefficient coefficient count index := by
  induction index with
  | zero =>
      simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient]
  | succ index ih =>
      rw [show index + 1 + 1 = (index + 1) + 1 by omega,
        Finset.sum_range_succ, ih,
        zeroPaddedBackwardDifference_eq_current_sub_previous]
      simp [zeroPaddedPreviousCoefficient]

/-- Every interior coefficient is reconstructed by the prefix of the returned difference. -/
theorem sum_zeroPaddedBackwardDifference_eq_coefficient
    (coefficient : ℕ → ℂ) (count index : ℕ) (hindex : index < count) :
    (∑ position ∈ Finset.range (index + 1),
        zeroPaddedBackwardDifference coefficient count position) = coefficient index := by
  rw [sum_zeroPaddedBackwardDifference_eq_zeroPaddedCoefficient]
  simp [zeroPaddedCoefficient, hindex]

/-- The complete finite coefficient mass is bounded by the aperture length times the complete
mass of its returned first difference. -/
theorem sum_norm_le_mul_sum_norm_zeroPaddedBackwardDifference
    (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range count, ‖coefficient index‖) ≤
      (count : ℝ) *
        ∑ position ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference coefficient count position‖ := by
  let returnedMass : ℝ :=
    ∑ position ∈ Finset.range (count + 1),
      ‖zeroPaddedBackwardDifference coefficient count position‖
  have hpoint (index : ℕ) (hindex : index ∈ Finset.range count) :
      ‖coefficient index‖ ≤ returnedMass := by
    have hinside : index < count := Finset.mem_range.mp hindex
    rw [← sum_zeroPaddedBackwardDifference_eq_coefficient
      coefficient count index hinside]
    calc
      _ ≤ ∑ position ∈ Finset.range (index + 1),
          ‖zeroPaddedBackwardDifference coefficient count position‖ :=
        norm_sum_le _ _
      _ ≤ returnedMass := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.range_mono (by omega)
        · intro position _hfull _hprefix
          exact norm_nonneg _
  calc
    _ ≤ ∑ _index ∈ Finset.range count, returnedMass := by
      exact Finset.sum_le_sum fun index hindex ↦ hpoint index hindex
    _ = (count : ℝ) * returnedMass := by simp

/-- Two exact prefix gluings reconstruct a finite coefficient from its zero-padded second
difference.  The factor `count * (count + 1)` is the complete retained reconstruction cost. -/
theorem sum_norm_le_mul_sum_norm_zeroPaddedSecondDifference
    (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range count, ‖coefficient index‖) ≤
      (count : ℝ) * (count + 1 : ℕ) *
        ∑ position ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count position‖ := by
  calc
    _ ≤ (count : ℝ) *
        ∑ position ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference coefficient count position‖ :=
      sum_norm_le_mul_sum_norm_zeroPaddedBackwardDifference coefficient count
    _ ≤ (count : ℝ) * ((count + 1 : ℕ) *
        ∑ position ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count position‖) := by
      gcongr
      simpa [zeroPaddedSecondDifference] using
        sum_norm_le_mul_sum_norm_zeroPaddedBackwardDifference
          (zeroPaddedBackwardDifference coefficient count) (count + 1)
    _ = (count : ℝ) * (count + 1 : ℕ) *
        ∑ position ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count position‖ := by ring

/-- Exact finite Fubini rotation placing the first coordinate innermost. -/
theorem threefold_sum_rotate_first
    {α β γ M : Type*} [AddCommMonoid M]
    (sα : Finset α) (sβ : Finset β) (sγ : Finset γ)
    (f : α → β → γ → M) :
    (∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, f a b c) =
      ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ a ∈ sα, f a b c := by
  calc
    _ = ∑ b ∈ sβ, ∑ a ∈ sα, ∑ c ∈ sγ, f a b c := Finset.sum_comm
    _ = ∑ b ∈ sβ, ∑ c ∈ sγ, ∑ a ∈ sα, f a b c := by
      apply Finset.sum_congr rfl
      intro b _
      exact Finset.sum_comm

/-- Exact finite Fubini rotation placing the second coordinate innermost. -/
theorem threefold_sum_rotate_second
    {α β γ M : Type*} [AddCommMonoid M]
    (sα : Finset α) (sβ : Finset β) (sγ : Finset γ)
    (f : α → β → γ → M) :
    (∑ a ∈ sα, ∑ b ∈ sβ, ∑ c ∈ sγ, f a b c) =
      ∑ a ∈ sα, ∑ c ∈ sγ, ∑ b ∈ sβ, f a b c := by
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- First-coordinate finite reconstruction, retaining both zero-padding boundary residues. -/
theorem threefold_sum_norm_le_first_secondDifference
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖coefficient firstIndex secondIndex thirdIndex‖) ≤
      (firstCount : ℝ) * (firstCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range (firstCount + 2),
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
                firstIndex secondIndex thirdIndex‖ := by
  let factor : ℝ := (firstCount : ℝ) * (firstCount + 1 : ℕ)
  rw [threefold_sum_rotate_first]
  calc
    _ ≤ ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          factor * ∑ firstIndex ∈ Finset.range (firstCount + 2),
            ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
              firstIndex secondIndex thirdIndex‖ := by
      apply Finset.sum_le_sum
      intro secondIndex _
      apply Finset.sum_le_sum
      intro thirdIndex _
      exact sum_norm_le_mul_sum_norm_zeroPaddedSecondDifference
        (fun firstIndex ↦ coefficient firstIndex secondIndex thirdIndex) firstCount
    _ = factor * ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ∑ firstIndex ∈ Finset.range (firstCount + 2),
            ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
              firstIndex secondIndex thirdIndex‖ := by
      simp only [Finset.mul_sum]
    _ = factor *
        ∑ firstIndex ∈ Finset.range (firstCount + 2),
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
                firstIndex secondIndex thirdIndex‖ := by
      apply congrArg (factor * ·)
      exact (threefold_sum_rotate_first
        (Finset.range (firstCount + 2)) (Finset.range secondCount)
        (Finset.range thirdCount)
        (fun firstIndex secondIndex thirdIndex ↦
          ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
            firstIndex secondIndex thirdIndex‖)).symm
    _ = (firstCount : ℝ) * (firstCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range (firstCount + 2),
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖zeroPaddedSecondDifferenceFirst coefficient firstCount
                firstIndex secondIndex thirdIndex‖ := rfl

/-- Second-coordinate finite reconstruction, retaining both zero-padding boundary residues. -/
theorem threefold_sum_norm_le_second_secondDifference
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖coefficient firstIndex secondIndex thirdIndex‖) ≤
      (secondCount : ℝ) * (secondCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range (secondCount + 2),
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖zeroPaddedSecondDifferenceSecond coefficient secondCount
                firstIndex secondIndex thirdIndex‖ := by
  let factor : ℝ := (secondCount : ℝ) * (secondCount + 1 : ℕ)
  rw [threefold_sum_rotate_second]
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range firstCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          factor * ∑ secondIndex ∈ Finset.range (secondCount + 2),
            ‖zeroPaddedSecondDifferenceSecond coefficient secondCount
              firstIndex secondIndex thirdIndex‖ := by
      apply Finset.sum_le_sum
      intro firstIndex _
      apply Finset.sum_le_sum
      intro thirdIndex _
      exact sum_norm_le_mul_sum_norm_zeroPaddedSecondDifference
        (fun secondIndex ↦ coefficient firstIndex secondIndex thirdIndex) secondCount
    _ = factor * ∑ firstIndex ∈ Finset.range firstCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ∑ secondIndex ∈ Finset.range (secondCount + 2),
            ‖zeroPaddedSecondDifferenceSecond coefficient secondCount
              firstIndex secondIndex thirdIndex‖ := by
      simp only [Finset.mul_sum]
    _ = (secondCount : ℝ) * (secondCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range (secondCount + 2),
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖zeroPaddedSecondDifferenceSecond coefficient secondCount
                firstIndex secondIndex thirdIndex‖ := by
      apply congrArg (factor * ·)
      exact (threefold_sum_rotate_second
        (Finset.range firstCount) (Finset.range (secondCount + 2))
        (Finset.range thirdCount)
        (fun firstIndex secondIndex thirdIndex ↦
          ‖zeroPaddedSecondDifferenceSecond coefficient secondCount
            firstIndex secondIndex thirdIndex‖)).symm

/-- Third-coordinate finite reconstruction, retaining both zero-padding boundary residues. -/
theorem threefold_sum_norm_le_third_secondDifference
    (coefficient : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖coefficient firstIndex secondIndex thirdIndex‖) ≤
      (thirdCount : ℝ) * (thirdCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range (thirdCount + 2),
              ‖zeroPaddedSecondDifferenceThird coefficient thirdCount
                firstIndex secondIndex thirdIndex‖ := by
  let factor : ℝ := (thirdCount : ℝ) * (thirdCount + 1 : ℕ)
  calc
    _ ≤ ∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          factor * ∑ thirdIndex ∈ Finset.range (thirdCount + 2),
            ‖zeroPaddedSecondDifferenceThird coefficient thirdCount
              firstIndex secondIndex thirdIndex‖ := by
      apply Finset.sum_le_sum
      intro firstIndex _
      apply Finset.sum_le_sum
      intro secondIndex _
      exact sum_norm_le_mul_sum_norm_zeroPaddedSecondDifference
        (coefficient firstIndex secondIndex) thirdCount
    _ = factor *
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range (thirdCount + 2),
              ‖zeroPaddedSecondDifferenceThird coefficient thirdCount
                firstIndex secondIndex thirdIndex‖ := by
      simp only [Finset.mul_sum]
    _ = (thirdCount : ℝ) * (thirdCount + 1 : ℕ) *
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range (thirdCount + 2),
              ‖zeroPaddedSecondDifferenceThird coefficient thirdCount
                firstIndex secondIndex thirdIndex‖ := rfl

/-- First- and second-coordinate zero-padded second differences commute on the complete finite
population, including all boundary addresses. -/
theorem zeroPaddedSecondDifferenceFirst_second_comm
    (coefficient : ℕ → ℕ → ℕ → ℂ) (firstCount secondCount : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    zeroPaddedSecondDifferenceFirst
        (zeroPaddedSecondDifferenceSecond coefficient secondCount)
        firstCount firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifferenceSecond
        (zeroPaddedSecondDifferenceFirst coefficient firstCount)
        secondCount firstIndex secondIndex thirdIndex := by
  unfold zeroPaddedSecondDifferenceFirst zeroPaddedSecondDifferenceSecond
  exact zeroPaddedMixedSecondDifference_comm
    (fun firstPosition secondPosition ↦
      coefficient firstPosition secondPosition thirdIndex)
    firstCount secondCount firstIndex secondIndex

/-! ## Reconstruction edges in the Boolean receiver cube -/

/-- The `{0,1}` Boolean face is exactly the established first/second zero-padded population. -/
theorem dyadicHodgeSubsetMass_firstSecond_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicHodgeCubeSecondDifferenceFirstSecond scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference, dyadicHodgeCubeSecondDifferenceFirstSecond]

/-- The `{1,2}` Boolean face is exactly the established second/third population. -/
theorem dyadicHodgeSubsetMass_secondThird_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({1, 2} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicHodgeCubeSecondDifferenceSecondThird scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference, dyadicHodgeCubeSecondDifferenceSecondThird]

/-- The `{0,2}` Boolean face is exactly the established first/third population. -/
theorem dyadicHodgeSubsetMass_firstThird_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({0, 2} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicHodgeCubeSecondDifferenceFirstThird scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference, dyadicHodgeCubeSecondDifferenceFirstThird]

/-- Removing the first-coordinate difference reconstructs the `{1,2}` face from the full face
with its exact finite gluing cost. -/
theorem dyadicHodgeSubsetMass_secondThird_le_full
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({1, 2} : CoordinateFace 3)
        scale component coordinate input ≤
      (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
          scale component coordinate input := by
  rw [dyadicHodgeSubsetMass_secondThird_eq,
    dyadicHodgeSubsetMass_univ_eq_allAxisMass]
  exact threefold_sum_norm_le_first_secondDifference
    (zeroPaddedSecondDifferenceSecond
      (zeroPaddedSecondDifferenceThird
        (dyadicHodgeCubeCoefficient scale component coordinate input)
        (dyadicHodgeApertureCount scale))
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale + 2)
    (dyadicHodgeApertureCount scale + 2)

/-- Removing the second-coordinate difference reconstructs the `{0,2}` face from the full face
with its exact finite gluing cost. -/
theorem dyadicHodgeSubsetMass_firstThird_le_full
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({0, 2} : CoordinateFace 3)
        scale component coordinate input ≤
      (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
          scale component coordinate input := by
  rw [dyadicHodgeSubsetMass_firstThird_eq,
    dyadicHodgeSubsetMass_univ_eq_allAxisMass]
  have hreconstruct := threefold_sum_norm_le_second_secondDifference
    (zeroPaddedSecondDifferenceFirst
      (zeroPaddedSecondDifferenceThird
        (dyadicHodgeCubeCoefficient scale component coordinate input)
        (dyadicHodgeApertureCount scale))
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale + 2)
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale + 2)
  have hmass :
      (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖zeroPaddedSecondDifferenceSecond
              (zeroPaddedSecondDifferenceFirst
                (zeroPaddedSecondDifferenceThird
                  (dyadicHodgeCubeCoefficient scale component coordinate input)
                  (dyadicHodgeApertureCount scale))
                (dyadicHodgeApertureCount scale))
              (dyadicHodgeApertureCount scale)
              firstIndex secondIndex thirdIndex‖) =
        ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
              ‖dyadicHodgeCubeSecondDifferenceAll scale component coordinate input
                firstIndex secondIndex thirdIndex‖ := by
    apply Finset.sum_congr rfl
    intro firstIndex _
    apply Finset.sum_congr rfl
    intro secondIndex _
    apply Finset.sum_congr rfl
    intro thirdIndex _
    rw [← zeroPaddedSecondDifferenceFirst_second_comm]
    rfl
  calc
    _ ≤ _ := hreconstruct
    _ = _ := congrArg
      ((dyadicHodgeApertureCount scale : ℝ) *
        (dyadicHodgeApertureCount scale + 1 : ℕ) * ·) hmass

/-- The `{2}` Boolean face is exactly the third-coordinate second-difference population. -/
theorem dyadicHodgeSubsetMass_third_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({2} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ‖dyadicHodgeCubeSecondDifferenceThird scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference, dyadicHodgeCubeSecondDifferenceThird]

/-- The `{1}` Boolean face is exactly the second-coordinate second-difference population. -/
theorem dyadicHodgeSubsetMass_second_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({1} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicHodgeCubeSecondDifferenceSecond scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference, dyadicHodgeCubeSecondDifferenceSecond]

/-- The `{0}` Boolean face is exactly the first-coordinate second-difference population. -/
theorem dyadicHodgeSubsetMass_first_eq
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({0} : CoordinateFace 3)
        scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖zeroPaddedSecondDifferenceFirst
              (dyadicHodgeCubeCoefficient scale component coordinate input)
              (dyadicHodgeApertureCount scale) firstIndex secondIndex thirdIndex‖ := by
  simp [dyadicHodgeSubsetMass, dyadicHodgeSubsetCount,
    dyadicHodgeCubeSubsetDifference]

/-- Removing the second-coordinate difference reconstructs `{2}` from `{1,2}`. -/
theorem dyadicHodgeSubsetMass_third_le_secondThird
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({2} : CoordinateFace 3)
        scale component coordinate input ≤
      (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({1, 2} : CoordinateFace 3)
          scale component coordinate input := by
  rw [dyadicHodgeSubsetMass_third_eq, dyadicHodgeSubsetMass_secondThird_eq]
  exact threefold_sum_norm_le_second_secondDifference
    (zeroPaddedSecondDifferenceThird
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale + 2)

/-- Removing the first-coordinate difference reconstructs `{1}` from `{0,1}`. -/
theorem dyadicHodgeSubsetMass_second_le_firstSecond
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({1} : CoordinateFace 3)
        scale component coordinate input ≤
      (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
          scale component coordinate input := by
  rw [dyadicHodgeSubsetMass_second_eq, dyadicHodgeSubsetMass_firstSecond_eq]
  exact threefold_sum_norm_le_first_secondDifference
    (zeroPaddedSecondDifferenceSecond
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale + 2)
    (dyadicHodgeApertureCount scale)

/-- Removing the second-coordinate difference reconstructs `{0}` from `{0,1}`; commutation is
the exact interchange cell which changes the coordinate order without changing the boundary. -/
theorem dyadicHodgeSubsetMass_first_le_firstSecond
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass ({0} : CoordinateFace 3)
        scale component coordinate input ≤
      (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
          scale component coordinate input := by
  rw [dyadicHodgeSubsetMass_first_eq, dyadicHodgeSubsetMass_firstSecond_eq]
  have hreconstruct := threefold_sum_norm_le_second_secondDifference
    (zeroPaddedSecondDifferenceFirst
      (dyadicHodgeCubeCoefficient scale component coordinate input)
      (dyadicHodgeApertureCount scale))
    (dyadicHodgeApertureCount scale + 2)
    (dyadicHodgeApertureCount scale)
    (dyadicHodgeApertureCount scale)
  calc
    _ ≤ _ := hreconstruct
    _ = _ := by
      apply congrArg
        ((dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) * ·)
      apply Finset.sum_congr rfl
      intro firstIndex _
      apply Finset.sum_congr rfl
      intro secondIndex _
      apply Finset.sum_congr rfl
      intro thirdIndex _
      rw [← zeroPaddedSecondDifferenceFirst_second_comm]
      rfl

/-- Every Boolean-face mass is nonnegative because it is the complete finite sum of norms. -/
theorem dyadicHodgeSubsetMass_nonneg
    (face : CoordinateFace 3) (scale : ℕ) (component coordinate input : Fin 3) :
    0 ≤ dyadicHodgeSubsetMass face scale component coordinate input := by
  unfold dyadicHodgeSubsetMass
  positivity

/-- The empty Boolean face is exactly the natural zero-order coefficient population. -/
theorem dyadicHodgeSubsetMass_empty_eq_coefficientMass
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass (∅ : CoordinateFace 3) scale component coordinate input =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖dyadicHodgeCubeCoefficient scale component coordinate input
              firstIndex secondIndex thirdIndex‖ := by
  rfl

/-- The direct aperture count is bounded by eight copies of its originating dyadic radius. -/
theorem dyadicHodgeApertureCount_le_eight_mul_radius (scale : ℕ) :
    dyadicHodgeApertureCount scale ≤ 8 * dyadicRadius scale := by
  rw [dyadicHodgeApertureCount_eq]
  have hradius : dyadicRadius (scale + 3) = 8 * dyadicRadius scale := by
    simp [dyadicRadius, pow_add, mul_comm]
  rw [hradius]
  omega

/-- One reconstructed coordinate costs at most `72 R²` at dyadic radius `R`.  Both factors come
from the exact two-prefix gluing; `8R` and `9R` are proved aperture bounds, not estimates. -/
theorem dyadicHodgeApertureReconstructionFactor_le (scale : ℕ) :
    (dyadicHodgeApertureCount scale : ℝ) *
        (dyadicHodgeApertureCount scale + 1 : ℕ) ≤
      72 * (dyadicRadius scale : ℝ) ^ 2 := by
  have hcount := dyadicHodgeApertureCount_le_eight_mul_radius scale
  have hradius : 1 ≤ dyadicRadius scale := by
    unfold dyadicRadius
    exact one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hsuccessor :
      dyadicHodgeApertureCount scale + 1 ≤ 9 * dyadicRadius scale := by
    omega
  exact_mod_cast (show
    dyadicHodgeApertureCount scale * (dyadicHodgeApertureCount scale + 1) ≤
      72 * dyadicRadius scale ^ 2 by
    calc
      _ ≤ (8 * dyadicRadius scale) * (9 * dyadicRadius scale) :=
        Nat.mul_le_mul hcount hsuccessor
      _ = 72 * dyadicRadius scale ^ 2 := by ring)

/-- The empty official receiver has its required cubic scale with exact numerator `512`. -/
theorem dyadicHodgeSubsetMass_empty_le
    (scale : ℕ) (component coordinate input : Fin 3) :
    dyadicHodgeSubsetMass (∅ : CoordinateFace 3) scale component coordinate input ≤
      512 * coordinateSubsetScale (dyadicRadius scale : ℝ) (∅ : CoordinateFace 3) := by
  rw [dyadicHodgeSubsetMass_empty_eq_coefficientMass]
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) ^ 3 :=
      sum_norm_dyadicHodgeCubeCoefficient_le_count_cube
        scale component coordinate input
    _ ≤ (8 * (dyadicRadius scale : ℝ)) ^ 3 := by
      gcongr
      exact_mod_cast dyadicHodgeApertureCount_le_eight_mul_radius scale
    _ = 512 * coordinateSubsetScale
        (dyadicRadius scale : ℝ) (∅ : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      ring

/-- The `{0,1}` official receiver has its required inverse-linear scale with the exact established
two-axis numerator. -/
theorem dyadicHodgeSubsetMass_firstSecond_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
        scale component coordinate input ≤
      34000000000000 * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0, 1} : CoordinateFace 3) := by
  rw [dyadicHodgeSubsetMass_firstSecond_eq]
  have hmass := sum_norm_dyadicHodgeCubeSecondDifferenceFirstSecond_le
    scale component coordinate input hscale
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ 34000000000000 / (dyadicRadius scale : ℝ) := hmass
    _ = 34000000000000 * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0, 1} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-- The `{1,2}` official receiver inherits its inverse-linear scale from the complete face by one
exact reconstruction. -/
theorem dyadicHodgeSubsetMass_secondThird_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({1, 2} : CoordinateFace 3)
        scale component coordinate input ≤
      (72 * 4119133228099520072) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({1, 2} : CoordinateFace 3) := by
  have hfactor := dyadicHodgeApertureReconstructionFactor_le scale
  have hfull := dyadicHodgeSubsetMass_univ_le_fullFaceRadial
    scale component coordinate input hscale
  have hmassNonneg := dyadicHodgeSubsetMass_nonneg
    (Finset.univ : CoordinateFace 3) scale component coordinate input
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
          scale component coordinate input :=
      dyadicHodgeSubsetMass_secondThird_le_full scale component coordinate input
    _ ≤ (72 * (dyadicRadius scale : ℝ) ^ 2) *
        (4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr
    _ = (72 * 4119133228099520072) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({1, 2} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-- The `{0,2}` official receiver inherits the same inverse-linear scale by the commuting
second-coordinate reconstruction. -/
theorem dyadicHodgeSubsetMass_firstThird_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({0, 2} : CoordinateFace 3)
        scale component coordinate input ≤
      (72 * 4119133228099520072) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0, 2} : CoordinateFace 3) := by
  have hfactor := dyadicHodgeApertureReconstructionFactor_le scale
  have hfull := dyadicHodgeSubsetMass_univ_le_fullFaceRadial
    scale component coordinate input hscale
  have hmassNonneg := dyadicHodgeSubsetMass_nonneg
    (Finset.univ : CoordinateFace 3) scale component coordinate input
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
          scale component coordinate input :=
      dyadicHodgeSubsetMass_firstThird_le_full scale component coordinate input
    _ ≤ (72 * (dyadicRadius scale : ℝ) ^ 2) *
        (4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3) := by
      gcongr
    _ = (72 * 4119133228099520072) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0, 2} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-- The `{1}` official receiver has the required linear scale after reconstructing one coordinate
from the established `{0,1}` face. -/
theorem dyadicHodgeSubsetMass_second_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({1} : CoordinateFace 3)
        scale component coordinate input ≤
      (72 * 34000000000000) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({1} : CoordinateFace 3) := by
  have hfactor := dyadicHodgeApertureReconstructionFactor_le scale
  have hpair := dyadicHodgeSubsetMass_firstSecond_le
    scale component coordinate input hscale
  have hpairNonneg := dyadicHodgeSubsetMass_nonneg
    ({0, 1} : CoordinateFace 3) scale component coordinate input
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
          scale component coordinate input :=
      dyadicHodgeSubsetMass_second_le_firstSecond scale component coordinate input
    _ ≤ (72 * (dyadicRadius scale : ℝ) ^ 2) *
        (34000000000000 * coordinateSubsetScale
          (dyadicRadius scale : ℝ) ({0, 1} : CoordinateFace 3)) := by
      gcongr
    _ = (72 * 34000000000000) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({1} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-- The `{0}` official receiver has the same required linear scale after the commuting
reconstruction from `{0,1}`. -/
theorem dyadicHodgeSubsetMass_first_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({0} : CoordinateFace 3)
        scale component coordinate input ≤
      (72 * 34000000000000) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0} : CoordinateFace 3) := by
  have hfactor := dyadicHodgeApertureReconstructionFactor_le scale
  have hpair := dyadicHodgeSubsetMass_firstSecond_le
    scale component coordinate input hscale
  have hpairNonneg := dyadicHodgeSubsetMass_nonneg
    ({0, 1} : CoordinateFace 3) scale component coordinate input
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({0, 1} : CoordinateFace 3)
          scale component coordinate input :=
      dyadicHodgeSubsetMass_first_le_firstSecond scale component coordinate input
    _ ≤ (72 * (dyadicRadius scale : ℝ) ^ 2) *
        (34000000000000 * coordinateSubsetScale
          (dyadicRadius scale : ℝ) ({0, 1} : CoordinateFace 3)) := by
      gcongr
    _ = (72 * 34000000000000) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({0} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-- The `{2}` official receiver has the required linear scale after the second exact
reconstruction in the full-face chain. -/
theorem dyadicHodgeSubsetMass_third_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale) :
    dyadicHodgeSubsetMass ({2} : CoordinateFace 3)
        scale component coordinate input ≤
      (72 * (72 * 4119133228099520072)) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({2} : CoordinateFace 3) := by
  have hfactor := dyadicHodgeApertureReconstructionFactor_le scale
  have hpair := dyadicHodgeSubsetMass_secondThird_le
    scale component coordinate input hscale
  have hpairNonneg := dyadicHodgeSubsetMass_nonneg
    ({1, 2} : CoordinateFace 3) scale component coordinate input
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale + 1 : ℕ) *
        dyadicHodgeSubsetMass ({1, 2} : CoordinateFace 3)
          scale component coordinate input :=
      dyadicHodgeSubsetMass_third_le_secondThird scale component coordinate input
    _ ≤ (72 * (dyadicRadius scale : ℝ) ^ 2) *
        ((72 * 4119133228099520072) * coordinateSubsetScale
          (dyadicRadius scale : ℝ) ({1, 2} : CoordinateFace 3)) := by
      gcongr
    _ = (72 * (72 * 4119133228099520072)) * coordinateSubsetScale
        (dyadicRadius scale : ℝ) ({2} : CoordinateFace 3) := by
      simp [coordinateSubsetScale]
      field_simp [hradius]

/-! ## The completed common receiver -/

/-- One exact common numerator for all eight Boolean faces.  It is the largest constructed face
constant, attained by the two-step `{0,1,2} → {1,2} → {2}` reconstruction chain. -/
def dyadicHodgeUniformSubsetMassConstant : ℝ :=
  72 * (72 * 4119133228099520072)

/-- **[proved-derived]** Every Boolean face of every large dyadic Hodge entry obeys its exact
coordinate-subset scale with one source-specific constant. -/
theorem dyadicHodgeSubsetMass_all_faces_le
    (scale : ℕ) (component coordinate input : Fin 3) (hscale : 3 ≤ scale)
    (face : CoordinateFace 3) :
    dyadicHodgeSubsetMass face scale component coordinate input ≤
      dyadicHodgeUniformSubsetMassConstant *
        coordinateSubsetScale (dyadicRadius scale : ℝ) face := by
  classical
  have hscaleNonneg (addressedFace : CoordinateFace 3) :
      0 ≤ coordinateSubsetScale (dyadicRadius scale : ℝ) addressedFace := by
    unfold coordinateSubsetScale
    positivity
  have hpromote (addressedFace : CoordinateFace 3) (constant : ℝ)
      (hconstant : constant ≤ dyadicHodgeUniformSubsetMassConstant)
      (hbound : dyadicHodgeSubsetMass addressedFace scale component coordinate input ≤
        constant * coordinateSubsetScale (dyadicRadius scale : ℝ) addressedFace) :
      dyadicHodgeSubsetMass addressedFace scale component coordinate input ≤
        dyadicHodgeUniformSubsetMassConstant *
          coordinateSubsetScale (dyadicRadius scale : ℝ) addressedFace :=
    hbound.trans (mul_le_mul_of_nonneg_right hconstant (hscaleNonneg addressedFace))
  have hradius : (dyadicRadius scale : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero scale (by norm_num : (2 : ℕ) ≠ 0))
  have hfullScaled :
      dyadicHodgeSubsetMass (Finset.univ : CoordinateFace 3)
          scale component coordinate input ≤
        4119133228099520072 * coordinateSubsetScale
          (dyadicRadius scale : ℝ) (Finset.univ : CoordinateFace 3) := by
    calc
      _ ≤ 4119133228099520072 / (dyadicRadius scale : ℝ) ^ 3 :=
        dyadicHodgeSubsetMass_univ_le_fullFaceRadial
          scale component coordinate input hscale
      _ = 4119133228099520072 * coordinateSubsetScale
          (dyadicRadius scale : ℝ) (Finset.univ : CoordinateFace 3) := by
        simp [coordinateSubsetScale]
        field_simp [hradius]
  by_cases hzero : (0 : Fin 3) ∈ face
  · by_cases hone : (1 : Fin 3) ∈ face
    · by_cases htwo : (2 : Fin 3) ∈ face
      · have hface : face = Finset.univ := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote (Finset.univ : CoordinateFace 3) 4119133228099520072
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          hfullScaled
      · have hface : face = {0, 1} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({0, 1} : CoordinateFace 3) 34000000000000
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_firstSecond_le
            scale component coordinate input hscale)
    · by_cases htwo : (2 : Fin 3) ∈ face
      · have hface : face = {0, 2} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({0, 2} : CoordinateFace 3) (72 * 4119133228099520072)
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_firstThird_le
            scale component coordinate input hscale)
      · have hface : face = {0} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({0} : CoordinateFace 3) (72 * 34000000000000)
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_first_le
            scale component coordinate input hscale)
  · by_cases hone : (1 : Fin 3) ∈ face
    · by_cases htwo : (2 : Fin 3) ∈ face
      · have hface : face = {1, 2} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({1, 2} : CoordinateFace 3) (72 * 4119133228099520072)
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_secondThird_le
            scale component coordinate input hscale)
      · have hface : face = {1} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({1} : CoordinateFace 3) (72 * 34000000000000)
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_second_le
            scale component coordinate input hscale)
    · by_cases htwo : (2 : Fin 3) ∈ face
      · have hface : face = {2} := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote ({2} : CoordinateFace 3)
          (72 * (72 * 4119133228099520072))
          (by rfl)
          (dyadicHodgeSubsetMass_third_le
            scale component coordinate input hscale)
      · have hface : face = ∅ := by
          ext axis
          fin_cases axis <;> simp_all
        subst face
        exact hpromote (∅ : CoordinateFace 3) 512
          (by norm_num [dyadicHodgeUniformSubsetMassConstant])
          (dyadicHodgeSubsetMass_empty_le scale component coordinate input)

/-- **[proved-derived]** The formerly uninhabited large-scale eight-face coefficient interface
now has a source-specific inhabitant. -/
theorem uniformLargeScaleDyadicHodgeSubsetMassReturn_inhabited :
    UniformLargeScaleDyadicHodgeSubsetMassReturn
      dyadicHodgeUniformSubsetMassConstant := by
  refine ⟨by norm_num [dyadicHodgeUniformSubsetMassConstant], ?_⟩
  intro scale hscale component coordinate input
  refine ⟨by norm_num [dyadicHodgeUniformSubsetMassConstant], ?_⟩
  exact dyadicHodgeSubsetMass_all_faces_le
    scale component coordinate input hscale

/-- **[proved-derived]** The completed eight-face return constructs the named uniform physical
dyadic Hodge kernel carrier. -/
theorem uniformDyadicHodgeJacobianKernelBound_inhabited :
    UniformDyadicHodgeJacobianKernelBound
      (804357 + 216 * dyadicHodgeUniformSubsetMassConstant) :=
  uniformDyadicHodgeJacobianKernelBound_of_subsetMassReturn
    uniformLargeScaleDyadicHodgeSubsetMassReturn_inhabited

section Audit

#print axioms sum_zeroPaddedBackwardDifference_eq_zeroPaddedCoefficient
#print axioms sum_norm_le_mul_sum_norm_zeroPaddedSecondDifference
#print axioms zeroPaddedSecondDifferenceFirst_second_comm
#print axioms dyadicHodgeSubsetMass_secondThird_le_full
#print axioms dyadicHodgeSubsetMass_firstThird_le_full
#print axioms dyadicHodgeSubsetMass_third_le_secondThird
#print axioms dyadicHodgeSubsetMass_second_le_firstSecond
#print axioms dyadicHodgeSubsetMass_first_le_firstSecond
#print axioms dyadicHodgeSubsetMass_empty_eq_coefficientMass
#print axioms dyadicHodgeApertureCount_le_eight_mul_radius
#print axioms dyadicHodgeApertureReconstructionFactor_le
#print axioms dyadicHodgeSubsetMass_empty_le
#print axioms dyadicHodgeSubsetMass_firstSecond_eq
#print axioms dyadicHodgeSubsetMass_firstSecond_le
#print axioms dyadicHodgeSubsetMass_secondThird_le
#print axioms dyadicHodgeSubsetMass_firstThird_le
#print axioms dyadicHodgeSubsetMass_first_le
#print axioms dyadicHodgeSubsetMass_second_le
#print axioms dyadicHodgeSubsetMass_third_le
#print axioms dyadicHodgeSubsetMass_all_faces_le
#print axioms uniformLargeScaleDyadicHodgeSubsetMassReturn_inhabited
#print axioms uniformDyadicHodgeJacobianKernelBound_inhabited

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeRemainingSubsetMasses
