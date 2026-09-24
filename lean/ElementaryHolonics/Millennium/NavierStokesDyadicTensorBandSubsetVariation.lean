import ElementaryHolonics.Millennium.NavierStokesDyadicTensorBandVariation
import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation

/-!
# Coordinate-subset variation of the direct dyadic tensor band

**[proved-derived]** The two-axis Hodge product rule needs every scalar subset order, not only
the top `2 × 2` face.  This owner retains the genuine common aperture and proves the missing
first-order translation law before forming the direct next-minus-base tensor populations.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation

/-! ## First variation survives the exact aperture translation -/

theorem zeroPaddedBackwardDifference_shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hshift : 1 ≤ shift) (hbig : count + 2 * shift ≤ bigCount) :
    zeroPaddedBackwardDifference
        (shiftedZeroExtension coefficient count shift) bigCount (shift + index) =
      zeroPaddedBackwardDifference coefficient count index := by
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPaddedCoefficient_shiftedZeroExtension_add coefficient count bigCount
      shift index hbig,
    zeroPaddedPreviousCoefficient_shiftedZeroExtension_add coefficient count bigCount
      shift index hshift hbig]

theorem zeroPaddedBackwardDifference_shiftedZeroExtension_eq_zero_of_lt
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : index < shift) :
    zeroPaddedBackwardDifference
      (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_lt
      coefficient count bigCount shift index hindex]
  have hprevious :
      zeroPaddedPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
    unfold zeroPaddedPreviousCoefficient
    split_ifs with hzero
    · rfl
    · exact zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_lt
        coefficient count bigCount shift (index - 1) (by omega)
  rw [hprevious]
  ring

theorem zeroPaddedBackwardDifference_shiftedZeroExtension_eq_zero_of_right
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : shift + count + 1 ≤ index) :
    zeroPaddedBackwardDifference
      (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
      coefficient count bigCount shift index (by omega)]
  have hprevious :
      zeroPaddedPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
    unfold zeroPaddedPreviousCoefficient
    rw [if_neg (by omega)]
    exact zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
      coefficient count bigCount shift (index - 1) (by omega)
  rw [hprevious]
  ring

/-- Total first variation is invariant under the same genuine two-flank translation. -/
theorem sum_norm_zeroPaddedBackwardDifference_shiftedZeroExtension
    (coefficient : ℕ → ℂ) (count shift : ℕ) (hshift : 1 ≤ shift) :
    (∑ index ∈ Finset.range (count + 2 * shift + 1),
      ‖zeroPaddedBackwardDifference
        (shiftedZeroExtension coefficient count shift)
        (count + 2 * shift) index‖) =
      ∑ index ∈ Finset.range (count + 1),
        ‖zeroPaddedBackwardDifference coefficient count index‖ := by
  rw [show count + 2 * shift + 1 = shift + (count + 1 + shift) by omega,
    Finset.sum_range_add]
  have hleft :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedBackwardDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) index‖) = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    rw [zeroPaddedBackwardDifference_shiftedZeroExtension_eq_zero_of_lt]
    · simp
    · simpa using hindex
  rw [hleft, zero_add]
  rw [show count + 1 + shift = (count + 1) + shift by omega,
    Finset.sum_range_add]
  have hmiddle :
      (∑ index ∈ Finset.range (count + 1),
        ‖zeroPaddedBackwardDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + index)‖) =
        ∑ index ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference coefficient count index‖ := by
    apply Finset.sum_congr rfl
    intro index _hindex
    rw [zeroPaddedBackwardDifference_shiftedZeroExtension_add
      coefficient count (count + 2 * shift) shift index hshift (by omega)]
  rw [hmiddle]
  have hright :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedBackwardDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + (count + 1) + index)‖) = 0 := by
    apply Finset.sum_eq_zero
    intro index _hindex
    rw [zeroPaddedBackwardDifference_shiftedZeroExtension_eq_zero_of_right]
    · simp
    · omega
  have hright' :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedBackwardDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + (count + 1 + index))‖) = 0 := by
    simpa [Nat.add_assoc] using hright
  rw [hright', add_zero]

theorem sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four
    (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ‖zeroPaddedBackwardDifference (dyadicNextCoordinateSlice scale)
        (dyadicHodgeApertureCount scale) index‖) ≤ 4 := by
  have hfunction : dyadicNextCoordinateSlice scale =
      centeredCoordinateValleePoussinSlice
        (dyadicHodgeParameter (scale + 1)) := by
    funext index
    exact dyadicNextCoordinateSlice_eq_centered scale index
  rw [hfunction, dyadicHodgeApertureCount_eq_nextProfileCount]
  exact
    sum_norm_zeroPaddedBackwardDifference_centeredCoordinateValleePoussinSlice_le_four
      (dyadicHodgeParameter (scale + 1))

theorem sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four
    (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ‖zeroPaddedBackwardDifference (dyadicBaseCoordinateSlice scale)
        (dyadicHodgeApertureCount scale) index‖) ≤ 4 := by
  have hfunction : dyadicBaseCoordinateSlice scale =
      shiftedZeroExtension
        (centeredCoordinateValleePoussinSlice (dyadicHodgeParameter scale))
        (dyadicBaseProfileCount scale) (dyadicProfileShift scale) := by
    funext index
    exact dyadicBaseCoordinateSlice_eq_shifted scale index
  have hshift : 1 ≤ dyadicProfileShift scale :=
    le_trans (by norm_num) (dyadicProfileShift_ge_two scale)
  rw [hfunction, dyadicHodgeApertureCount_eq_base_add_two_shift,
    sum_norm_zeroPaddedBackwardDifference_shiftedZeroExtension
      (centeredCoordinateValleePoussinSlice (dyadicHodgeParameter scale))
      (dyadicBaseProfileCount scale) (dyadicProfileShift scale)
      hshift,
    dyadicBaseProfileCount_eq]
  exact
    sum_norm_zeroPaddedBackwardDifference_centeredCoordinateValleePoussinSlice_le_four
      (dyadicHodgeParameter scale)

/-! ## Every scalar coordinate-subset population -/

/-- Orders `0`, `1`, and `2` select the coefficient, first backward difference, and second
backward difference respectively.  Higher orders are deliberately collapsed to zero; only the
three explicitly proved Abel faces are admitted below. -/
def zeroPaddedVariation (order : ℕ) (coefficient : ℕ → ℂ)
    (count index : ℕ) : ℂ :=
  match order with
  | 0 => coefficient index
  | 1 => zeroPaddedBackwardDifference coefficient count index
  | 2 => zeroPaddedSecondDifference coefficient count index
  | _ => 0

def separatedDyadicProfileSubsetVariation
    (scale firstOrder secondOrder : ℕ) (slice : ℕ → ℂ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (zeroPaddedVariation firstOrder slice (dyadicHodgeApertureCount scale))
    (zeroPaddedVariation secondOrder slice (dyadicHodgeApertureCount scale))
    slice firstIndex secondIndex thirdIndex

/-- The subtraction remains inside the direct band at every admitted coordinate subset. -/
def dyadicTensorBandSubsetVariation
    (scale firstOrder secondOrder firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedDyadicProfileSubsetVariation scale firstOrder secondOrder
      (dyadicNextCoordinateSlice scale) firstIndex secondIndex thirdIndex -
    separatedDyadicProfileSubsetVariation scale firstOrder secondOrder
      (dyadicBaseCoordinateSlice scale) firstIndex secondIndex thirdIndex

/-- Exact tensor Fubini bound for any selected subset orders, prior to inserting their scalar
variation estimates. -/
theorem sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    (scale firstOrder secondOrder : ℕ) :
    (∑ firstIndex ∈ Finset.range
        (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale firstOrder secondOrder
            firstIndex secondIndex thirdIndex‖) ≤
      ((∑ firstIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + firstOrder),
          ‖zeroPaddedVariation firstOrder (dyadicNextCoordinateSlice scale)
            (dyadicHodgeApertureCount scale) firstIndex‖) *
        (∑ secondIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + secondOrder),
          ‖zeroPaddedVariation secondOrder (dyadicNextCoordinateSlice scale)
            (dyadicHodgeApertureCount scale) secondIndex‖) *
        (∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicNextCoordinateSlice scale thirdIndex‖)) +
      ((∑ firstIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + firstOrder),
          ‖zeroPaddedVariation firstOrder (dyadicBaseCoordinateSlice scale)
            (dyadicHodgeApertureCount scale) firstIndex‖) *
        (∑ secondIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + secondOrder),
          ‖zeroPaddedVariation secondOrder (dyadicBaseCoordinateSlice scale)
            (dyadicHodgeApertureCount scale) secondIndex‖) *
        (∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicBaseCoordinateSlice scale thirdIndex‖)) := by
  let next := separatedDyadicProfileSubsetVariation scale firstOrder secondOrder
    (dyadicNextCoordinateSlice scale)
  let base := separatedDyadicProfileSubsetVariation scale firstOrder secondOrder
    (dyadicBaseCoordinateSlice scale)
  change (∑ firstIndex ∈ Finset.range
        (dyadicHodgeApertureCount scale + firstOrder),
      ∑ secondIndex ∈ Finset.range
          (dyadicHodgeApertureCount scale + secondOrder),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖next firstIndex secondIndex thirdIndex -
            base firstIndex secondIndex thirdIndex‖) ≤ _
  refine (sum_sum_sum_norm_sub_le next base
    (dyadicHodgeApertureCount scale + firstOrder)
    (dyadicHodgeApertureCount scale + secondOrder)
    (dyadicHodgeApertureCount scale)).trans ?_
  dsimp [next, base, separatedDyadicProfileSubsetVariation]
  rw [sum_norm_separatedTensorCoefficient,
    sum_norm_separatedTensorCoefficient]

theorem sum_norm_dyadicTensorBandSubsetVariation_zero_zero_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 0 0
            firstIndex secondIndex thirdIndex‖) ≤
      2 * (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 0 0).trans ?_
  simp only [Nat.add_zero, zeroPaddedVariation]
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  calc
    _ ≤ (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) +
        (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) := by gcongr
    _ = 2 * (dyadicHodgeApertureCount scale : ℝ) ^ 3 := by ring

theorem sum_norm_dyadicTensorBandSubsetVariation_one_zero_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 0
            firstIndex secondIndex thirdIndex‖) ≤
      8 * (dyadicHodgeApertureCount scale : ℝ) ^ 2 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 1 0).trans ?_
  simp only [zeroPaddedVariation, Nat.add_zero]
  have hnextFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four scale
  have hbaseFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four scale
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  calc
    _ ≤ 4 * (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) +
        4 * (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) := by gcongr
    _ = 8 * (dyadicHodgeApertureCount scale : ℝ) ^ 2 := by ring

theorem sum_norm_dyadicTensorBandSubsetVariation_two_zero_le_precise
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 0
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 2 0).trans ?_
  simp only [zeroPaddedVariation, Nat.add_zero]
  have hnextSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice scale)
  have hbaseSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice scale)
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  calc
    _ ≤ (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) *
          (dyadicHodgeApertureCount scale : ℝ) := by gcongr
    _ = (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 := by ring

theorem sum_norm_dyadicTensorBandSubsetVariation_one_one_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 1
            firstIndex secondIndex thirdIndex‖) ≤
      32 * (dyadicHodgeApertureCount scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 1 1).trans ?_
  simp only [zeroPaddedVariation]
  have hnextFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four scale
  have hbaseFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four scale
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  calc
    _ ≤ 4 * 4 * (dyadicHodgeApertureCount scale : ℝ) +
        4 * 4 * (dyadicHodgeApertureCount scale : ℝ) := by gcongr
    _ = 32 * (dyadicHodgeApertureCount scale : ℝ) := by ring

theorem sum_norm_dyadicTensorBandSubsetVariation_one_two_le_precise
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 2
            firstIndex secondIndex thirdIndex‖) ≤
      4 * (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) +
        4 * (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 1 2).trans ?_
  simp only [zeroPaddedVariation]
  have hnextFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four scale
  have hbaseFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four scale
  have hnextSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice scale)
  have hbaseSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice scale)
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  gcongr

theorem sum_norm_dyadicTensorBandSubsetVariation_two_one_le_precise
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 1
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) * 4 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) * 4 *
          (dyadicHodgeApertureCount scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 2 1).trans ?_
  simp only [zeroPaddedVariation]
  have hnextFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicNextCoordinateSlice_le_four scale
  have hbaseFirst :=
    sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four scale
  have hnextSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice scale)
  have hbaseSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice scale)
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  gcongr

theorem sum_norm_dyadicTensorBandSubsetVariation_two_two_le_precise
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 2
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_le_profile_masses
    scale 2 2).trans ?_
  simp only [zeroPaddedVariation]
  have hnextSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice scale)
  have hbaseSecond :=
    le_of_eq (sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice scale)
  have hnext := sum_norm_dyadicNextCoordinateSlice_le_count scale
  have hbase := sum_norm_dyadicBaseCoordinateSlice_le_count scale
  calc
    _ ≤ (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (4 / (dyadicHodgeParameter scale + 1 : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) := by gcongr
    _ = _ := by ring

/-! ## Explicit dyadic scalings -/

theorem dyadicHodgeApertureCount_le_eight_mul_radius (scale : ℕ) :
    dyadicHodgeApertureCount scale ≤ 8 * dyadicRadius scale := by
  rw [dyadicHodgeApertureCount_eq]
  have hscale : dyadicRadius (scale + 3) = 8 * dyadicRadius scale := by
    simp only [dyadicRadius,
      show scale + 3 = ((scale + 1) + 1) + 1 by omega, pow_succ]
    ring
  rw [hscale]
  omega

theorem dyadicHodgeApertureCount_real_le_eight_mul_radius (scale : ℕ) :
    (dyadicHodgeApertureCount scale : ℝ) ≤
      8 * (dyadicRadius scale : ℝ) := by
  exact_mod_cast dyadicHodgeApertureCount_le_eight_mul_radius scale

theorem dyadicHodgeParameter_base_real_eq_radius (scale : ℕ) :
    (dyadicHodgeParameter scale + 1 : ℝ) = dyadicRadius scale := by
  exact_mod_cast dyadicHodgeParameter_add_one scale

theorem dyadicHodgeParameter_next_real_eq_two_mul_radius (scale : ℕ) :
    (dyadicHodgeParameter (scale + 1) + 1 : ℝ) =
      2 * (dyadicRadius scale : ℝ) := by
  rw [show (dyadicHodgeParameter (scale + 1) + 1 : ℝ) =
    dyadicRadius (scale + 1) by
      exact_mod_cast dyadicHodgeParameter_add_one (scale + 1)]
  simp only [dyadicRadius, pow_succ]
  push_cast
  ring

theorem sum_norm_dyadicTensorBandSubsetVariation_zero_zero_le_1024_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 0 0
            firstIndex secondIndex thirdIndex‖) ≤
      1024 * (dyadicRadius scale : ℝ) ^ 3 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_zero_zero_le scale).trans ?_
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  calc
    2 * (dyadicHodgeApertureCount scale : ℝ) ^ 3 ≤
      2 * (8 * (dyadicRadius scale : ℝ)) ^ 3 := by gcongr
    _ = 1024 * (dyadicRadius scale : ℝ) ^ 3 := by ring

theorem sum_norm_dyadicTensorBandSubsetVariation_one_zero_le_512_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 0
            firstIndex secondIndex thirdIndex‖) ≤
      512 * (dyadicRadius scale : ℝ) ^ 2 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_one_zero_le scale).trans ?_
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  nlinarith [sq_nonneg ((dyadicHodgeApertureCount scale : ℝ) -
    8 * (dyadicRadius scale : ℝ))]

theorem sum_norm_dyadicTensorBandSubsetVariation_two_zero_le_384_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 0
            firstIndex secondIndex thirdIndex‖) ≤
      384 * (dyadicRadius scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_two_zero_le_precise scale).trans ?_
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  rw [dyadicHodgeParameter_next_real_eq_two_mul_radius,
    dyadicHodgeParameter_base_real_eq_radius]
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  calc
    (4 / (2 * (dyadicRadius scale : ℝ))) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 +
        (4 / (dyadicRadius scale : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ^ 2 ≤
      (4 / (2 * (dyadicRadius scale : ℝ))) *
          (8 * (dyadicRadius scale : ℝ)) ^ 2 +
        (4 / (dyadicRadius scale : ℝ)) *
          (8 * (dyadicRadius scale : ℝ)) ^ 2 := by gcongr
    _ = 384 * (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicTensorBandSubsetVariation_one_one_le_256_mul
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 1
            firstIndex secondIndex thirdIndex‖) ≤
      256 * (dyadicRadius scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_one_one_le scale).trans ?_
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  nlinarith

theorem sum_norm_dyadicTensorBandSubsetVariation_one_two_le_192
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 1 2
            firstIndex secondIndex thirdIndex‖) ≤ 192 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_one_two_le_precise scale).trans ?_
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  rw [dyadicHodgeParameter_next_real_eq_two_mul_radius,
    dyadicHodgeParameter_base_real_eq_radius]
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  calc
    4 * (4 / (2 * (dyadicRadius scale : ℝ))) *
          (dyadicHodgeApertureCount scale : ℝ) +
        4 * (4 / (dyadicRadius scale : ℝ)) *
          (dyadicHodgeApertureCount scale : ℝ) ≤
      4 * (4 / (2 * (dyadicRadius scale : ℝ))) *
          (8 * (dyadicRadius scale : ℝ)) +
        4 * (4 / (dyadicRadius scale : ℝ)) *
          (8 * (dyadicRadius scale : ℝ)) := by gcongr
    _ = 192 := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicTensorBandSubsetVariation_two_one_le_192
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 1),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 1
            firstIndex secondIndex thirdIndex‖) ≤ 192 := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_two_one_le_precise scale).trans ?_
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  rw [dyadicHodgeParameter_next_real_eq_two_mul_radius,
    dyadicHodgeParameter_base_real_eq_radius]
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  calc
    (4 / (2 * (dyadicRadius scale : ℝ))) * 4 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicRadius scale : ℝ)) * 4 *
          (dyadicHodgeApertureCount scale : ℝ) ≤
      (4 / (2 * (dyadicRadius scale : ℝ))) * 4 *
          (8 * (dyadicRadius scale : ℝ)) +
        (4 / (dyadicRadius scale : ℝ)) * 4 *
          (8 * (dyadicRadius scale : ℝ)) := by gcongr
    _ = 192 := by
      field_simp [hradius.ne']
      ring

theorem sum_norm_dyadicTensorBandSubsetVariation_two_two_le_160_div
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSubsetVariation scale 2 2
            firstIndex secondIndex thirdIndex‖) ≤
      160 / (dyadicRadius scale : ℝ) := by
  refine (sum_norm_dyadicTensorBandSubsetVariation_two_two_le_precise scale).trans ?_
  have hradius : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  rw [dyadicHodgeParameter_next_real_eq_two_mul_radius,
    dyadicHodgeParameter_base_real_eq_radius]
  have hcount := dyadicHodgeApertureCount_real_le_eight_mul_radius scale
  calc
    (4 / (2 * (dyadicRadius scale : ℝ))) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicRadius scale : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) ≤
      (4 / (2 * (dyadicRadius scale : ℝ))) ^ 2 *
          (8 * (dyadicRadius scale : ℝ)) +
        (4 / (dyadicRadius scale : ℝ)) ^ 2 *
          (8 * (dyadicRadius scale : ℝ)) := by gcongr
    _ = 160 / (dyadicRadius scale : ℝ) := by
      field_simp [hradius.ne']
      ring

section Audit

#print axioms sum_norm_zeroPaddedBackwardDifference_shiftedZeroExtension
#print axioms sum_norm_zeroPaddedBackwardDifference_dyadicBaseCoordinateSlice_le_four

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation
