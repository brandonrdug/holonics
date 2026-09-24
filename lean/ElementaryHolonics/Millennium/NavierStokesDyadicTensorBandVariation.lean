import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeKernelVariation

/-!
# Direct dyadic tensor-band variation

**[proved-derived]** This owner computes coordinate-subset variation for the direct dyadic scalar
band on its genuine common aperture.  The smaller profile is translated into that aperture by an
exact zero extension; its boundary stencils are therefore retained rather than silently discarded.

This is the scalar half of the direct Hodge mixed-mass deed.  The rational Hodge interaction is
not replaced by a coefficient-count estimate here.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation

/-! ## Exact translation of a compact coefficient population -/

/-- Translate a finite coefficient population to the right, retaining zero extension on both
sides. -/
def shiftedZeroExtension
    (coefficient : ℕ → ℂ) (count shift index : ℕ) : ℂ :=
  if shift ≤ index then
    zeroPaddedCoefficient coefficient count (index - shift)
  else 0

@[simp]
theorem shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count shift index : ℕ) :
    shiftedZeroExtension coefficient count shift (shift + index) =
      zeroPaddedCoefficient coefficient count index := by
  simp [shiftedZeroExtension]

/-- A second difference commutes exactly with a translation by at least two positions. -/
theorem zeroPaddedCoefficient_shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hbig : count + 2 * shift ≤ bigCount) :
    zeroPaddedCoefficient (shiftedZeroExtension coefficient count shift)
        bigCount (shift + index) =
      zeroPaddedCoefficient coefficient count index := by
  by_cases hindex : index < count
  · have hposition : shift + index < bigCount := by omega
    simp [zeroPaddedCoefficient, shiftedZeroExtension, hindex, hposition]
  · by_cases hposition : shift + index < bigCount
    · simp [zeroPaddedCoefficient, shiftedZeroExtension, hindex, hposition]
    · simp [zeroPaddedCoefficient, hindex, hposition]

theorem zeroPaddedPreviousCoefficient_shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hshift : 1 ≤ shift) (hbig : count + 2 * shift ≤ bigCount) :
    zeroPaddedPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount (shift + index) =
      zeroPaddedPreviousCoefficient coefficient count index := by
  by_cases hzero : index = 0
  · subst index
    simp [zeroPaddedPreviousCoefficient, zeroPaddedCoefficient,
      shiftedZeroExtension]
    all_goals omega
  · have hrewrite : shift + index - 1 = shift + (index - 1) := by omega
    rw [zeroPaddedPreviousCoefficient, if_neg (by omega), hrewrite,
      zeroPaddedCoefficient_shiftedZeroExtension_add coefficient count bigCount
        shift (index - 1) hbig]
    simp [zeroPaddedPreviousCoefficient, hzero]

theorem zeroPaddedSecondPreviousCoefficient_shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hshift : 2 ≤ shift) (hbig : count + 2 * shift ≤ bigCount) :
    zeroPaddedSecondPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount (shift + index) =
      zeroPaddedSecondPreviousCoefficient coefficient count index := by
  by_cases hsmall : index < 2
  · interval_cases index <;>
      simp [zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient,
        shiftedZeroExtension] <;> omega
  · have hrewrite : shift + index - 2 = shift + (index - 2) := by omega
    rw [zeroPaddedSecondPreviousCoefficient, if_neg (by omega), hrewrite,
      zeroPaddedCoefficient_shiftedZeroExtension_add coefficient count bigCount
        shift (index - 2) hbig]
    simp [zeroPaddedSecondPreviousCoefficient, hsmall]

theorem zeroPaddedSecondDifference_shiftedZeroExtension_add
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hshift : 2 ≤ shift)
    (hbig : count + 2 * shift ≤ bigCount) :
    zeroPaddedSecondDifference
        (shiftedZeroExtension coefficient count shift) bigCount (shift + index) =
      zeroPaddedSecondDifference coefficient count index := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedCoefficient_shiftedZeroExtension_add coefficient count bigCount
      shift index hbig,
    zeroPaddedPreviousCoefficient_shiftedZeroExtension_add coefficient count bigCount
      shift index (by omega) hbig,
    zeroPaddedSecondPreviousCoefficient_shiftedZeroExtension_add
      coefficient count bigCount shift index hshift hbig]

theorem zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_lt
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : index < shift) :
    zeroPaddedCoefficient (shiftedZeroExtension coefficient count shift)
      bigCount index = 0 := by
  simp [zeroPaddedCoefficient, shiftedZeroExtension, hindex]

theorem zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : shift + count ≤ index) :
    zeroPaddedCoefficient (shiftedZeroExtension coefficient count shift)
      bigCount index = 0 := by
  by_cases hbig : index < bigCount
  · simp [zeroPaddedCoefficient, shiftedZeroExtension, hbig]
    all_goals omega
  · simp [zeroPaddedCoefficient, hbig]

/-- Before the translated population, its zero-padded second difference is exactly zero. -/
theorem zeroPaddedSecondDifference_shiftedZeroExtension_eq_zero_of_lt
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : index < shift) :
    zeroPaddedSecondDifference
      (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients,
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
  have hsecondPrevious :
      zeroPaddedSecondPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
    unfold zeroPaddedSecondPreviousCoefficient
    split_ifs with hsmall
    · rfl
    · exact zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_lt
        coefficient count bigCount shift (index - 2) (by omega)
  rw [hprevious, hsecondPrevious]
  ring

/-- Two positions beyond the translated population, every second-difference stencil is zero. -/
theorem zeroPaddedSecondDifference_shiftedZeroExtension_eq_zero_of_right
    (coefficient : ℕ → ℂ) (count bigCount shift index : ℕ)
    (hindex : shift + count + 2 ≤ index) :
    zeroPaddedSecondDifference
      (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
      coefficient count bigCount shift index (by omega)]
  have hprevious :
      zeroPaddedPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
    unfold zeroPaddedPreviousCoefficient
    rw [if_neg (by omega)]
    exact zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
      coefficient count bigCount shift (index - 1) (by omega)
  have hsecondPrevious :
      zeroPaddedSecondPreviousCoefficient
        (shiftedZeroExtension coefficient count shift) bigCount index = 0 := by
    unfold zeroPaddedSecondPreviousCoefficient
    rw [if_neg (by omega)]
    exact zeroPaddedCoefficient_shiftedZeroExtension_eq_zero_of_right
      coefficient count bigCount shift (index - 2) (by omega)
  rw [hprevious, hsecondPrevious]
  ring

/-- Total second variation is invariant under a zero-padded translation inside a larger aperture. -/
theorem sum_norm_zeroPaddedSecondDifference_shiftedZeroExtension
    (coefficient : ℕ → ℂ) (count shift : ℕ)
    (hshift : 2 ≤ shift) :
    (∑ index ∈ Finset.range (count + 2 * shift + 2),
      ‖zeroPaddedSecondDifference
        (shiftedZeroExtension coefficient count shift)
        (count + 2 * shift) index‖) =
      ∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference coefficient count index‖ := by
  rw [show count + 2 * shift + 2 = shift + (count + 2 + shift) by omega,
    Finset.sum_range_add]
  have hleft :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedSecondDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) index‖) = 0 := by
    apply Finset.sum_eq_zero
    intro index hindex
    rw [zeroPaddedSecondDifference_shiftedZeroExtension_eq_zero_of_lt]
    · simp
    · simpa using hindex
  rw [hleft, zero_add]
  rw [show count + 2 + shift = (count + 2) + shift by omega,
    Finset.sum_range_add]
  have hmiddle :
      (∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + index)‖) =
        ∑ index ∈ Finset.range (count + 2),
          ‖zeroPaddedSecondDifference coefficient count index‖ := by
    apply Finset.sum_congr rfl
    intro index _hindex
    rw [zeroPaddedSecondDifference_shiftedZeroExtension_add
      coefficient count (count + 2 * shift) shift index hshift (by omega)]
  rw [hmiddle]
  have hright :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedSecondDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + (count + 2) + index)‖) = 0 := by
    apply Finset.sum_eq_zero
    intro index _hindex
    rw [zeroPaddedSecondDifference_shiftedZeroExtension_eq_zero_of_right]
    · simp
    · omega
  have hright' :
      (∑ index ∈ Finset.range shift,
        ‖zeroPaddedSecondDifference
          (shiftedZeroExtension coefficient count shift)
          (count + 2 * shift) (shift + (count + 2 + index))‖) = 0 := by
    simpa [Nat.add_assoc] using hright
  rw [hright', add_zero]

/-! ## The two dyadic scalar profiles in their common aperture -/

/-- The centered scalar chart at the next dyadic parameter. -/
def dyadicNextCoordinateSlice (scale index : ℕ) : ℂ :=
  (coordinateValleePoussinWeight (dyadicHodgeParameter (scale + 1))
    (centeredFrequency (dyadicHodgeApertureRadius scale) index) : ℂ)

/-- The centered scalar chart at the base dyadic parameter, transported into the next aperture. -/
def dyadicBaseCoordinateSlice (scale index : ℕ) : ℂ :=
  (coordinateValleePoussinWeight (dyadicHodgeParameter scale)
    (centeredFrequency (dyadicHodgeApertureRadius scale) index) : ℂ)

/-- Outer-radius displacement between the two consecutive dyadic profiles. -/
def dyadicProfileShift (scale : ℕ) : ℕ :=
  dyadicHodgeOuterCutoff (scale + 1) - dyadicHodgeOuterCutoff scale

theorem dyadicProfileShift_eq (scale : ℕ) :
    dyadicProfileShift scale = dyadicRadius (scale + 1) := by
  rw [dyadicProfileShift, dyadicHodgeOuterCutoff_eq,
    dyadicHodgeOuterCutoff_eq]
  have hpow : dyadicRadius (scale + 2) =
      2 * dyadicRadius (scale + 1) := by
    simp only [dyadicRadius, show scale + 2 = (scale + 1) + 1 by omega, pow_succ]
    ring
  rw [hpow]
  have hpositive : 1 ≤ dyadicRadius (scale + 1) := by
    exact Nat.one_le_pow (scale + 1) 2 (by norm_num)
  omega

theorem dyadicProfileShift_ge_two (scale : ℕ) :
    2 ≤ dyadicProfileShift scale := by
  rw [dyadicProfileShift_eq]
  change 2 ^ 1 ≤ 2 ^ (scale + 1)
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- Exact smaller-profile population count. -/
def dyadicBaseProfileCount (scale : ℕ) : ℕ :=
  centeredFrequencyCount (dyadicHodgeOuterCutoff scale)

/-- The common aperture is the base population plus its two zero flanks. -/
theorem dyadicHodgeApertureCount_eq_base_add_two_shift (scale : ℕ) :
    dyadicHodgeApertureCount scale =
      dyadicBaseProfileCount scale + 2 * dyadicProfileShift scale := by
  unfold dyadicHodgeApertureCount dyadicHodgeApertureRadius
    dyadicBaseProfileCount centeredFrequencyCount dyadicProfileShift
  have hmono := dyadicHodgeOuterCutoff_mono scale
  omega

/-- The next scalar chart is its ordinary centered profile on the common aperture. -/
theorem dyadicNextCoordinateSlice_eq_centered
    (scale index : ℕ) :
    dyadicNextCoordinateSlice scale index =
      centeredCoordinateValleePoussinSlice
        (dyadicHodgeParameter (scale + 1)) index := by
  unfold dyadicNextCoordinateSlice centeredCoordinateValleePoussinSlice
    dyadicHodgeApertureRadius dyadicHodgeOuterCutoff
  rfl

/-- The base scalar chart is exactly the shifted zero extension of its own centered profile. -/
theorem dyadicBaseCoordinateSlice_eq_shifted
    (scale index : ℕ) :
    dyadicBaseCoordinateSlice scale index =
      shiftedZeroExtension
        (centeredCoordinateValleePoussinSlice (dyadicHodgeParameter scale))
        (dyadicBaseProfileCount scale) (dyadicProfileShift scale) index := by
  have hmono := dyadicHodgeOuterCutoff_mono scale
  by_cases hleft : dyadicProfileShift scale ≤ index
  · rw [shiftedZeroExtension, if_pos hleft]
    by_cases hinterior : index - dyadicProfileShift scale <
        dyadicBaseProfileCount scale
    · rw [zeroPaddedCoefficient, if_pos hinterior]
      unfold dyadicBaseCoordinateSlice centeredCoordinateValleePoussinSlice
      congr 2
      unfold centeredFrequency
      have hshiftCast :
          (dyadicProfileShift scale : ℤ) =
            (dyadicHodgeOuterCutoff (scale + 1) : ℤ) -
              (dyadicHodgeOuterCutoff scale : ℤ) := by
        unfold dyadicProfileShift
        rw [Nat.cast_sub hmono]
      have hindexCast :
          ((index - dyadicProfileShift scale : ℕ) : ℤ) =
            (index : ℤ) - (dyadicProfileShift scale : ℤ) := by
        rw [Nat.cast_sub hleft]
      rw [hindexCast, hshiftCast]
      unfold dyadicHodgeApertureRadius dyadicHodgeOuterCutoff
      ring
    · rw [zeroPaddedCoefficient, if_neg hinterior]
      have hcenter : dyadicHodgeApertureRadius scale ≤ index := by
        unfold dyadicHodgeApertureRadius dyadicBaseProfileCount
          dyadicProfileShift centeredFrequencyCount at *
        omega
      have habs := natAbs_centeredFrequency_of_ge hcenter
      have houtside :
          valleePoussinOuterRadius (dyadicHodgeParameter scale) <
            (centeredFrequency (dyadicHodgeApertureRadius scale) index).natAbs := by
        rw [habs]
        unfold dyadicHodgeApertureRadius dyadicBaseProfileCount
          dyadicProfileShift centeredFrequencyCount dyadicHodgeOuterCutoff at *
        omega
      unfold dyadicBaseCoordinateSlice
      rw [coordinateValleePoussinWeight_eq_zero_of_outer_lt _ houtside]
      norm_num
  · rw [shiftedZeroExtension, if_neg hleft]
    have hcenter : index ≤ dyadicHodgeApertureRadius scale := by
      unfold dyadicHodgeApertureRadius dyadicProfileShift at *
      omega
    have habs := natAbs_centeredFrequency_of_le hcenter
    have houtside :
        valleePoussinOuterRadius (dyadicHodgeParameter scale) <
          (centeredFrequency (dyadicHodgeApertureRadius scale) index).natAbs := by
      rw [habs]
      unfold dyadicHodgeApertureRadius dyadicProfileShift dyadicHodgeOuterCutoff at *
      omega
    unfold dyadicBaseCoordinateSlice
    rw [coordinateValleePoussinWeight_eq_zero_of_outer_lt _ houtside]
    norm_num

/-- The next profile's native population is exactly the common aperture count. -/
theorem dyadicHodgeApertureCount_eq_nextProfileCount (scale : ℕ) :
    dyadicHodgeApertureCount scale =
      4 * dyadicHodgeParameter (scale + 1) + 3 := by
  unfold dyadicHodgeApertureCount dyadicHodgeApertureRadius
    centeredFrequencyCount dyadicHodgeOuterCutoff valleePoussinOuterRadius
  omega

/-- The base profile's native population count in its own aperture. -/
theorem dyadicBaseProfileCount_eq (scale : ℕ) :
    dyadicBaseProfileCount scale = 4 * dyadicHodgeParameter scale + 3 := by
  unfold dyadicBaseProfileCount centeredFrequencyCount dyadicHodgeOuterCutoff
    valleePoussinOuterRadius
  omega

/-- Exact reciprocal-scale second variation of the next dyadic scalar profile. -/
theorem sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice
    (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ‖zeroPaddedSecondDifference (dyadicNextCoordinateSlice scale)
        (dyadicHodgeApertureCount scale) index‖) =
      4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ) := by
  have hfunction : dyadicNextCoordinateSlice scale =
      centeredCoordinateValleePoussinSlice
        (dyadicHodgeParameter (scale + 1)) := by
    funext index
    exact dyadicNextCoordinateSlice_eq_centered scale index
  rw [hfunction, dyadicHodgeApertureCount_eq_nextProfileCount]
  exact sum_norm_zeroPaddedSecondDifference_centeredCoordinateValleePoussinSlice
    (dyadicHodgeParameter (scale + 1))

/-- Exact reciprocal-scale second variation of the transported base profile, including both
new zero flanks of the common aperture. -/
theorem sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice
    (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ‖zeroPaddedSecondDifference (dyadicBaseCoordinateSlice scale)
        (dyadicHodgeApertureCount scale) index‖) =
      4 / (dyadicHodgeParameter scale + 1 : ℝ) := by
  have hfunction : dyadicBaseCoordinateSlice scale =
      shiftedZeroExtension
        (centeredCoordinateValleePoussinSlice (dyadicHodgeParameter scale))
        (dyadicBaseProfileCount scale) (dyadicProfileShift scale) := by
    funext index
    exact dyadicBaseCoordinateSlice_eq_shifted scale index
  rw [hfunction, dyadicHodgeApertureCount_eq_base_add_two_shift]
  rw [sum_norm_zeroPaddedSecondDifference_shiftedZeroExtension
    (centeredCoordinateValleePoussinSlice (dyadicHodgeParameter scale))
    (dyadicBaseProfileCount scale) (dyadicProfileShift scale)
    (dyadicProfileShift_ge_two scale)]
  rw [dyadicBaseProfileCount_eq]
  exact sum_norm_zeroPaddedSecondDifference_centeredCoordinateValleePoussinSlice
    (dyadicHodgeParameter scale)

/-- Each scalar profile has coefficient mass at most the exact common aperture population. -/
theorem sum_norm_dyadicCoordinateSlice_le_count
    (slice : ℕ → ℂ)
    (hunit : ∀ index, ‖slice index‖ ≤ 1) (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale), ‖slice index‖) ≤
      (dyadicHodgeApertureCount scale : ℝ) := by
  calc
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale), ‖slice index‖) ≤
      ∑ _index ∈ Finset.range (dyadicHodgeApertureCount scale), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro index _hindex
        exact hunit index
    _ = (dyadicHodgeApertureCount scale : ℝ) := by simp

theorem norm_dyadicNextCoordinateSlice_le_one (scale index : ℕ) :
    ‖dyadicNextCoordinateSlice scale index‖ ≤ 1 := by
  unfold dyadicNextCoordinateSlice
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coordinateValleePoussinWeight_nonneg _ _)]
  exact coordinateValleePoussinWeight_le_one _ _

theorem norm_dyadicBaseCoordinateSlice_le_one (scale index : ℕ) :
    ‖dyadicBaseCoordinateSlice scale index‖ ≤ 1 := by
  unfold dyadicBaseCoordinateSlice
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coordinateValleePoussinWeight_nonneg _ _)]
  exact coordinateValleePoussinWeight_le_one _ _

theorem sum_norm_dyadicNextCoordinateSlice_le_count (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale),
      ‖dyadicNextCoordinateSlice scale index‖) ≤
      (dyadicHodgeApertureCount scale : ℝ) :=
  sum_norm_dyadicCoordinateSlice_le_count (dyadicNextCoordinateSlice scale)
    (norm_dyadicNextCoordinateSlice_le_one scale) scale

theorem sum_norm_dyadicBaseCoordinateSlice_le_count (scale : ℕ) :
    (∑ index ∈ Finset.range (dyadicHodgeApertureCount scale),
      ‖dyadicBaseCoordinateSlice scale index‖) ≤
      (dyadicHodgeApertureCount scale : ℝ) :=
  sum_norm_dyadicCoordinateSlice_le_count (dyadicBaseCoordinateSlice scale)
    (norm_dyadicBaseCoordinateSlice_le_one scale) scale

/-! ## Direct tensor band and its sharp two-coordinate variation -/

def dyadicNextTensorCubeCoefficient
    (scale firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale)
    (dyadicNextCoordinateSlice scale) firstIndex secondIndex thirdIndex

def dyadicBaseTensorCubeCoefficient
    (scale firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale)
    (dyadicBaseCoordinateSlice scale) firstIndex secondIndex thirdIndex

/-- The subtraction remains inside the scalar tensor band. -/
def dyadicTensorBandCubeCoefficient
    (scale firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  dyadicNextTensorCubeCoefficient scale firstIndex secondIndex thirdIndex -
    dyadicBaseTensorCubeCoefficient scale firstIndex secondIndex thirdIndex

theorem dyadicNextTensorCubeCoefficient_eq_actual
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicNextTensorCubeCoefficient scale firstIndex secondIndex thirdIndex =
      (tensorValleePoussinWeight (dyadicHodgeParameter (scale + 1))
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ) := by
  simp [dyadicNextTensorCubeCoefficient, separatedTensorCoefficient,
    dyadicNextCoordinateSlice, tensorValleePoussinWeight,
    dyadicHodgeApertureFrequency, Fin.prod_univ_three]

theorem dyadicBaseTensorCubeCoefficient_eq_actual
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicBaseTensorCubeCoefficient scale firstIndex secondIndex thirdIndex =
      (tensorValleePoussinWeight (dyadicHodgeParameter scale)
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ) := by
  simp [dyadicBaseTensorCubeCoefficient, separatedTensorCoefficient,
    dyadicBaseCoordinateSlice, tensorValleePoussinWeight,
    dyadicHodgeApertureFrequency, Fin.prod_univ_three]

/-- The natural-indexed direct tensor band is exactly the chain owner's direct band weight. -/
theorem dyadicTensorBandCubeCoefficient_eq_actual
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicTensorBandCubeCoefficient scale firstIndex secondIndex thirdIndex =
      (dyadicHodgeBandWeight scale
        (dyadicHodgeApertureFrequency scale firstIndex secondIndex thirdIndex) : ℂ) := by
  rw [dyadicTensorBandCubeCoefficient,
    dyadicNextTensorCubeCoefficient_eq_actual,
    dyadicBaseTensorCubeCoefficient_eq_actual]
  unfold dyadicHodgeBandWeight
  push_cast
  rfl

/-- Two-coordinate zero-padded second variation of the direct scalar tensor band. -/
def dyadicTensorBandSecondDifferenceFirstSecond
    (scale firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedMixedSecondDifference
    (fun firstPosition secondPosition ↦
      dyadicTensorBandCubeCoefficient scale
        firstPosition secondPosition thirdIndex)
    (dyadicHodgeApertureCount scale) (dyadicHodgeApertureCount scale)
    firstIndex secondIndex

theorem dyadicTensorBandSecondDifferenceFirstSecond_eq_sub
    (scale firstIndex secondIndex thirdIndex : ℕ) :
    dyadicTensorBandSecondDifferenceFirstSecond scale
        firstIndex secondIndex thirdIndex =
      separatedTensorSecondDifferenceFirstSecond
          (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale)
          (dyadicNextCoordinateSlice scale) (dyadicHodgeApertureCount scale)
          firstIndex secondIndex thirdIndex -
        separatedTensorSecondDifferenceFirstSecond
          (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale)
          (dyadicBaseCoordinateSlice scale) (dyadicHodgeApertureCount scale)
          firstIndex secondIndex thirdIndex := by
  unfold dyadicTensorBandSecondDifferenceFirstSecond
    dyadicTensorBandCubeCoefficient dyadicNextTensorCubeCoefficient
    dyadicBaseTensorCubeCoefficient
    separatedTensorSecondDifferenceFirstSecond
  exact zeroPaddedMixedSecondDifference_sub _ _ _ _ _ _

theorem sum_norm_dyadicNextTensorSecondDifferenceFirstSecond_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖separatedTensorSecondDifferenceFirstSecond
            (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale)
            (dyadicNextCoordinateSlice scale) (dyadicHodgeApertureCount scale)
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) ^ 2 *
        (dyadicHodgeApertureCount scale : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirstSecond,
    sum_norm_zeroPaddedSecondDifference_dyadicNextCoordinateSlice]
  rw [pow_two]
  gcongr
  exact sum_norm_dyadicNextCoordinateSlice_le_count scale

theorem sum_norm_dyadicBaseTensorSecondDifferenceFirstSecond_le
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖separatedTensorSecondDifferenceFirstSecond
            (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale)
            (dyadicBaseCoordinateSlice scale) (dyadicHodgeApertureCount scale)
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter scale + 1 : ℝ)) ^ 2 *
        (dyadicHodgeApertureCount scale : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirstSecond,
    sum_norm_zeroPaddedSecondDifference_dyadicBaseCoordinateSlice]
  rw [pow_two]
  gcongr
  exact sum_norm_dyadicBaseCoordinateSlice_le_count scale

/-- Exact direct-band two-coordinate scalar variation before scale simplification. -/
theorem sum_norm_dyadicTensorBandSecondDifferenceFirstSecond_le_precise
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSecondDifferenceFirstSecond scale
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) := by
  calc
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSecondDifferenceFirstSecond scale
            firstIndex secondIndex thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖separatedTensorSecondDifferenceFirstSecond
                (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale)
                (dyadicNextCoordinateSlice scale) (dyadicHodgeApertureCount scale)
                firstIndex secondIndex thirdIndex -
              separatedTensorSecondDifferenceFirstSecond
                (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale)
                (dyadicBaseCoordinateSlice scale) (dyadicHodgeApertureCount scale)
                firstIndex secondIndex thirdIndex‖ := by
        simp_rw [dyadicTensorBandSecondDifferenceFirstSecond_eq_sub]
    _ ≤
      (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
            ‖separatedTensorSecondDifferenceFirstSecond
              (dyadicNextCoordinateSlice scale) (dyadicNextCoordinateSlice scale)
              (dyadicNextCoordinateSlice scale) (dyadicHodgeApertureCount scale)
              firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
          ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
            ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
              ‖separatedTensorSecondDifferenceFirstSecond
                (dyadicBaseCoordinateSlice scale) (dyadicBaseCoordinateSlice scale)
                (dyadicBaseCoordinateSlice scale) (dyadicHodgeApertureCount scale)
                firstIndex secondIndex thirdIndex‖ :=
      sum_sum_sum_norm_sub_le _ _ _ _ _
    _ ≤ _ := add_le_add
      (sum_norm_dyadicNextTensorSecondDifferenceFirstSecond_le scale)
      (sum_norm_dyadicBaseTensorSecondDifferenceFirstSecond_le scale)

/-- The genuine direct scalar tensor band has the required reciprocal dyadic two-axis mass. -/
theorem sum_norm_dyadicTensorBandSecondDifferenceFirstSecond_le_160_div
    (scale : ℕ) :
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSecondDifferenceFirstSecond scale
            firstIndex secondIndex thirdIndex‖) ≤
      160 / (dyadicRadius scale : ℝ) := by
  have hradiusPositive : 0 < (dyadicRadius scale : ℝ) := by
    exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) scale)
  have hbaseScale :
      (dyadicHodgeParameter scale + 1 : ℝ) = dyadicRadius scale := by
    exact_mod_cast dyadicHodgeParameter_add_one scale
  have hnextScale :
      (dyadicHodgeParameter (scale + 1) + 1 : ℝ) =
        2 * (dyadicRadius scale : ℝ) := by
    rw [show (dyadicHodgeParameter (scale + 1) + 1 : ℝ) =
      dyadicRadius (scale + 1) by
        exact_mod_cast dyadicHodgeParameter_add_one (scale + 1)]
    simp only [dyadicRadius, pow_succ]
    push_cast
    ring
  have hcountNat :
      dyadicHodgeApertureCount scale ≤ 8 * dyadicRadius scale := by
    rw [dyadicHodgeApertureCount_eq]
    have hscale : dyadicRadius (scale + 3) = 8 * dyadicRadius scale := by
      simp only [dyadicRadius,
        show scale + 3 = ((scale + 1) + 1) + 1 by omega, pow_succ]
      ring
    rw [hscale]
    omega
  have hcount :
      (dyadicHodgeApertureCount scale : ℝ) ≤
        8 * (dyadicRadius scale : ℝ) := by
    exact_mod_cast hcountNat
  calc
    (∑ firstIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
      ∑ secondIndex ∈ Finset.range (dyadicHodgeApertureCount scale + 2),
        ∑ thirdIndex ∈ Finset.range (dyadicHodgeApertureCount scale),
          ‖dyadicTensorBandSecondDifferenceFirstSecond scale
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (dyadicHodgeParameter (scale + 1) + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) +
        (4 / (dyadicHodgeParameter scale + 1 : ℝ)) ^ 2 *
          (dyadicHodgeApertureCount scale : ℝ) :=
      sum_norm_dyadicTensorBandSecondDifferenceFirstSecond_le_precise scale
    _ ≤ (4 / (2 * (dyadicRadius scale : ℝ))) ^ 2 *
          (8 * (dyadicRadius scale : ℝ)) +
        (4 / (dyadicRadius scale : ℝ)) ^ 2 *
          (8 * (dyadicRadius scale : ℝ)) := by
      rw [hnextScale, hbaseScale]
      gcongr
    _ = 160 / (dyadicRadius scale : ℝ) := by
      field_simp [hradiusPositive.ne']
      ring

#print axioms sum_norm_zeroPaddedSecondDifference_shiftedZeroExtension
#print axioms dyadicBaseCoordinateSlice_eq_shifted
#print axioms sum_norm_dyadicTensorBandSecondDifferenceFirstSecond_le_160_div


end Soma.Holonics.Millennium.NavierStokesDyadicTensorBandVariation
