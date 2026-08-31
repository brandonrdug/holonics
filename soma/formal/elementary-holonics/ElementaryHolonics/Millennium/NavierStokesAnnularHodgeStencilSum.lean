import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation

/-!
# Boundary-resolved annular Hodge stencil sums

**[proved-derived]** This owner carries the localized rational Hodge estimates through the
zero-padded aperture.  The initial and terminal stencils are retained as addressed terms: no
mode-count estimate is used in their place.  The resulting one-coordinate receiver is the exact
input needed before opening mixed coordinate differences and physical Fubini.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeStencilSum

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation

/-! ## Tensor first variation -/

/-- The next tensor chart has total first variation at most four along every addressed axis. -/
theorem sum_norm_zeroPaddedBackwardDifference_nextTensorSlice_le_four
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference
        (nextTensorSliceInAdjacentAperture radius axis base)
        (4 * radius + 7) index‖) ≤ 4 := by
  have hslice :
      nextTensorSliceInAdjacentAperture radius axis base =
        fun index ↦ nextCoordinateSliceInAdjacentAperture radius index *
          (tensorCoordinateComplement (radius + 1) axis base : ℂ) := by
    funext index
    exact nextTensorSliceInAdjacentAperture_eq radius axis base index
  rw [hslice]
  simp_rw [zeroPaddedBackwardDifference_mul_right, norm_mul]
  calc
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ *
          ‖(tensorCoordinateComplement (radius + 1) axis base : ℂ)‖) ≤
      ∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ * 1 := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact mul_le_mul_of_nonneg_left
        (norm_tensorCoordinateComplement_le_one (radius + 1) axis base) (norm_nonneg _)
    _ ≤ 4 := by
      simpa using
        sum_norm_zeroPaddedBackwardDifference_nextCoordinateSliceInAdjacentAperture_le_four
          radius

/-- The transported base tensor chart has total first variation at most four. -/
theorem sum_norm_zeroPaddedBackwardDifference_baseTensorSlice_le_four
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference
        (baseTensorSliceInAdjacentAperture radius axis base)
        (4 * radius + 7) index‖) ≤ 4 := by
  have hslice :
      baseTensorSliceInAdjacentAperture radius axis base =
        fun index ↦ baseCoordinateSliceInAdjacentAperture radius index *
          (tensorCoordinateComplement radius axis base : ℂ) := by
    funext index
    exact baseTensorSliceInAdjacentAperture_eq radius axis base index
  rw [hslice]
  simp_rw [zeroPaddedBackwardDifference_mul_right, norm_mul]
  calc
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ *
          ‖(tensorCoordinateComplement radius axis base : ℂ)‖) ≤
      ∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ * 1 := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact mul_le_mul_of_nonneg_left
        (norm_tensorCoordinateComplement_le_one radius axis base) (norm_nonneg _)
    _ ≤ 4 := by
      simpa using
        sum_norm_zeroPaddedBackwardDifference_baseCoordinateSliceInAdjacentAperture_le_four
          radius

/-- The genuine adjacent tensor slice has scale-uniform total first variation. -/
theorem sum_norm_zeroPaddedBackwardDifference_adjacentTensorSlice_le_eight
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index‖) ≤ 8 := by
  have hpoint : ∀ index,
      zeroPaddedBackwardDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index =
        zeroPaddedBackwardDifference
            (nextTensorSliceInAdjacentAperture radius axis base)
            (4 * radius + 7) index -
          zeroPaddedBackwardDifference
            (baseTensorSliceInAdjacentAperture radius axis base)
            (4 * radius + 7) index := by
    intro index
    exact zeroPaddedBackwardDifference_sub _ _ _ _
  calc
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index‖) ≤
      (∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference
          (nextTensorSliceInAdjacentAperture radius axis base)
          (4 * radius + 7) index‖) +
      (∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference
          (baseTensorSliceInAdjacentAperture radius axis base)
          (4 * radius + 7) index‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro index _hindex
      rw [hpoint index]
      exact norm_sub_le _ _
    _ ≤ 4 + 4 := add_le_add
      (sum_norm_zeroPaddedBackwardDifference_nextTensorSlice_le_four radius axis base)
      (sum_norm_zeroPaddedBackwardDifference_baseTensorSlice_le_four radius axis base)
    _ = 8 := by norm_num

/-! ## Reindexing and exact terminal taper -/

/-- Consecutive centered indices are consecutive integer frequencies. -/
theorem centeredFrequency_succ (outer index : ℕ) :
    centeredFrequency outer (index + 1) = centeredFrequency outer index + 1 := by
  unfold centeredFrequency
  omega

/-- Reindexing one lattice step is exactly the localized coordinate increment. -/
theorem replaceFrequencyCoordinate_centered_succ
    (axis : Fin 3) (base : SpatialFrequency) (outer index : ℕ) :
    replaceFrequencyCoordinate axis base (centeredFrequency outer (index + 1)) =
      incrementFrequencyCoordinate axis
        (replaceFrequencyCoordinate axis base (centeredFrequency outer index)) := by
  funext other
  by_cases haxis : other = axis
  · subst other
    simp [replaceFrequencyCoordinate, centeredFrequency_succ]
  · simp [replaceFrequencyCoordinate, incrementFrequencyCoordinate, haxis]

/-- Two reindexed lattice steps are exactly the twice-incremented frequency. -/
theorem replaceFrequencyCoordinate_centered_add_two
    (axis : Fin 3) (base : SpatialFrequency) (outer index : ℕ) :
    replaceFrequencyCoordinate axis base (centeredFrequency outer (index + 2)) =
      twiceIncrementFrequencyCoordinate axis
        (replaceFrequencyCoordinate axis base (centeredFrequency outer index)) := by
  rw [show index + 2 = (index + 1) + 1 by omega,
    replaceFrequencyCoordinate_centered_succ,
    replaceFrequencyCoordinate_centered_succ]
  rfl

/-- Every internal adjacent-aperture index remains in the genuine outer frequency cube. -/
theorem replaceFrequencyCoordinate_centered_mem_outer
    (radius index : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (hbase : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (hindex : index < 4 * radius + 7) :
    replaceFrequencyCoordinate axis base
        (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index) ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)) := by
  rw [mem_frequencyCube_iff] at hbase ⊢
  intro other
  by_cases haxis : other = axis
  · subst other
    simp only [replaceFrequencyCoordinate, Function.update_self]
    unfold centeredFrequency valleePoussinOuterRadius
    constructor <;> omega
  · simpa [replaceFrequencyCoordinate, haxis] using hbase other

/-- A transverse coordinate outside the inner cube keeps every coordinate replacement outside. -/
theorem replaceFrequencyCoordinate_not_mem_inner_of_transverse
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (value : ℤ)
    (htransverse : ∃ other : Fin 3,
      other ≠ axis ∧ radius + 2 ≤ (base other).natAbs) :
    replaceFrequencyCoordinate axis base value ∉ frequencyCube (radius + 1) := by
  obtain ⟨other, hother, hlarge⟩ := htransverse
  intro hinner
  rw [mem_frequencyCube_iff] at hinner
  have hbound :
      -(radius + 1 : ℤ) ≤ base other ∧ base other ≤ (radius + 1 : ℤ) := by
    simpa [replaceFrequencyCoordinate, hother] using hinner other
  have habs : (base other).natAbs ≤ radius + 1 :=
    (natAbs_le_iff_bounds (radius + 1) (base other)).mpr hbound
  omega

/-- Exact final value of the next scalar taper in the common aperture. -/
theorem nextCoordinateSlice_terminal (radius : ℕ) :
    nextCoordinateSliceInAdjacentAperture radius (4 * radius + 6) =
      1 / (radius + 2 : ℂ) := by
  rw [nextCoordinateSliceInAdjacentAperture,
    centeredCoordinateValleePoussinSlice_eq_profile]
  convert centeredValleePoussinProfile_last (radius + 1) using 1
  all_goals push_cast
  all_goals ring_nf

/-- The penultimate next-radius taper coefficient is at most two reciprocal scale units. -/
theorem norm_nextCoordinateSlice_penultimate_le (radius : ℕ) :
    ‖nextCoordinateSliceInAdjacentAperture radius (4 * radius + 5)‖ ≤
      2 / (radius + 2 : ℝ) := by
  rw [nextCoordinateSliceInAdjacentAperture,
    centeredCoordinateValleePoussinSlice_eq_profile]
  by_cases hzero : radius = 0
  · subst radius
    norm_num [centeredValleePoussinProfile]
  · rw [centeredValleePoussinProfile_eq_right
      (show 3 * (radius + 1) + 2 < 4 * radius + 5 by omega)
      (show 4 * radius + 5 < 4 * (radius + 1) + 3 by omega)]
    have hnumerator : 4 * (radius + 1) + 3 - (4 * radius + 5) = 2 := by omega
    rw [hnumerator]
    have hdenominator : ((radius + 1 : ℕ) : ℂ) + 1 = (radius + 2 : ℕ) := by
      push_cast
      ring
    rw [hdenominator, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    norm_num

/-- The transported base chart is already zero at the penultimate common-aperture index. -/
theorem baseCoordinateSlice_penultimate (radius : ℕ) :
    baseCoordinateSliceInAdjacentAperture radius (4 * radius + 5) = 0 := by
  rw [baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo]
  simp [twoSidedPadTwo]

/-- The transported base chart is zero at the terminal common-aperture index. -/
theorem baseCoordinateSlice_terminal (radius : ℕ) :
    baseCoordinateSliceInAdjacentAperture radius (4 * radius + 6) = 0 := by
  rw [baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo]
  simp [twoSidedPadTwo]

/-- Terminal adjacent tensor mass is one reciprocal scale unit. -/
theorem norm_adjacentTensorSlice_terminal_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    ‖adjacentTensorSlice radius axis base (4 * radius + 6)‖ ≤
      1 / (radius + 2 : ℝ) := by
  rw [adjacentTensorSlice, nextTensorSliceInAdjacentAperture_eq,
    baseTensorSliceInAdjacentAperture_eq, nextCoordinateSlice_terminal,
    baseCoordinateSlice_terminal]
  simp only [zero_mul, sub_zero, norm_mul, norm_div, norm_one]
  have hdenominator : (radius : ℂ) + 2 = (radius + 2 : ℕ) := by
    push_cast
    ring
  rw [hdenominator, Complex.norm_natCast]
  have hscale : 0 ≤ 1 / (radius + 2 : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (norm_tensorCoordinateComplement_le_one (radius + 1) axis base) hscale
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one] using hmul

/-- Penultimate adjacent tensor mass is at most two reciprocal scale units. -/
theorem norm_adjacentTensorSlice_penultimate_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    ‖adjacentTensorSlice radius axis base (4 * radius + 5)‖ ≤
      2 / (radius + 2 : ℝ) := by
  rw [adjacentTensorSlice, nextTensorSliceInAdjacentAperture_eq,
    baseTensorSliceInAdjacentAperture_eq, baseCoordinateSlice_penultimate]
  simp only [zero_mul, sub_zero, norm_mul]
  calc
    ‖nextCoordinateSliceInAdjacentAperture radius (4 * radius + 5)‖ *
        ‖(tensorCoordinateComplement (radius + 1) axis base : ℂ)‖ ≤
      ‖nextCoordinateSliceInAdjacentAperture radius (4 * radius + 5)‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_tensorCoordinateComplement_le_one (radius + 1) axis base) (norm_nonneg _)
    _ ≤ 2 / (radius + 2 : ℝ) := by
      simpa using norm_nextCoordinateSlice_penultimate_le radius

/-- The final internal difference of the adjacent tensor slice is bounded by three reciprocal
scale units, retaining both endpoint coefficients. -/
theorem norm_adjacentTensorSlice_terminalDifference_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    ‖adjacentTensorSlice radius axis base (4 * radius + 6) -
        adjacentTensorSlice radius axis base (4 * radius + 5)‖ ≤
      3 / (radius + 2 : ℝ) := by
  calc
    ‖adjacentTensorSlice radius axis base (4 * radius + 6) -
        adjacentTensorSlice radius axis base (4 * radius + 5)‖ ≤
      ‖adjacentTensorSlice radius axis base (4 * radius + 6)‖ +
        ‖adjacentTensorSlice radius axis base (4 * radius + 5)‖ := norm_sub_le _ _
    _ ≤ 1 / (radius + 2 : ℝ) + 2 / (radius + 2 : ℝ) :=
      add_le_add (norm_adjacentTensorSlice_terminal_le radius axis base)
        (norm_adjacentTensorSlice_penultimate_le radius axis base)
    _ = 3 / (radius + 2 : ℝ) := by ring

/-! ## Exact aperture identities -/

theorem zeroPadded_firstDifference_eq_internal
    (coefficient : ℕ → ℂ) (count index : ℕ)
    (hpositive : 0 < index) (hindex : index < count) :
    zeroPaddedCoefficient coefficient count index -
        zeroPaddedPreviousCoefficient coefficient count index =
      coefficient index - coefficient (index - 1) := by
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient, hindex,
    show index ≠ 0 by omega, show index - 1 < count by omega]

theorem zeroPadded_secondDifference_eq_internal
    (coefficient : ℕ → ℂ) (count index : ℕ)
    (htwo : 2 ≤ index) (hindex : index < count) :
    zeroPaddedSecondDifference coefficient count index =
      coefficient index - 2 * coefficient (index - 1) + coefficient (index - 2) := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients]
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    zeroPaddedSecondPreviousCoefficient, hindex,
    show index ≠ 0 by omega, show index - 1 < count by omega,
    show ¬index < 2 by omega, show index - 2 < count by omega]

/-- At the first nonzero stencil, the shifted first-factor passage is exactly the left endpoint. -/
theorem zeroPadded_shiftedFirstDifference_at_one
    (coefficient : ℕ → ℂ) (count : ℕ) (hcount : 0 < count) :
    zeroPaddedPreviousCoefficient coefficient count 1 -
        zeroPaddedSecondPreviousCoefficient coefficient count 1 = coefficient 0 := by
  simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
    zeroPaddedCoefficient, hcount]

/-- At the first point beyond support, the shifted passage is the terminal internal difference. -/
theorem zeroPadded_shiftedFirstDifference_at_count
    (coefficient : ℕ → ℂ) (count : ℕ) (htwo : 2 ≤ count) :
    zeroPaddedPreviousCoefficient coefficient count count -
        zeroPaddedSecondPreviousCoefficient coefficient count count =
      coefficient (count - 1) - coefficient (count - 2) := by
  simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
    zeroPaddedCoefficient, show count ≠ 0 by omega, show ¬count < 2 by omega,
    show count - 1 < count by omega, show count - 2 < count by omega]

theorem zeroPadded_firstDifference_at_count
    (coefficient : ℕ → ℂ) (count : ℕ) (hcount : 0 < count) :
    zeroPaddedCoefficient coefficient count count -
        zeroPaddedPreviousCoefficient coefficient count count =
      -coefficient (count - 1) := by
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    show count ≠ 0 by omega, show count - 1 < count by omega]

theorem zeroPadded_firstDifference_at_count_add_one
    (coefficient : ℕ → ℂ) (count : ℕ) :
    zeroPaddedCoefficient coefficient count (count + 1) -
        zeroPaddedPreviousCoefficient coefficient count (count + 1) = 0 := by
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient]

theorem zeroPadded_secondDifference_at_count
    (coefficient : ℕ → ℂ) (count : ℕ) (htwo : 2 ≤ count) :
    zeroPaddedSecondDifference coefficient count count =
      -2 * coefficient (count - 1) + coefficient (count - 2) := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients]
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    zeroPaddedSecondPreviousCoefficient, show count ≠ 0 by omega,
    show ¬count < 2 by omega, show count - 1 < count by omega,
    show count - 2 < count by omega]

theorem zeroPadded_secondDifference_at_count_add_one
    (coefficient : ℕ → ℂ) (count : ℕ) (hcount : 0 < count) :
    zeroPaddedSecondDifference coefficient count (count + 1) =
      coefficient (count - 1) := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients]
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    zeroPaddedSecondPreviousCoefficient, show ¬count + 1 < 2 by omega,
    show count + 1 - 2 = count - 1 by omega, show count - 1 < count by omega]

/-! ## A boundary-resolved product sum -/

/-- Boundary-resolved zero-padded product estimate.  Rational first and second differences are
required only on genuine internal stencils.  The two left/right aperture passages appear as four
explicit scalar endpoint terms instead of being spread over the whole coefficient population. -/
theorem sum_norm_zeroPaddedSecondDifference_mul_le_of_internal
    (first second : ℕ → ℂ) (count : ℕ) (htwo : 2 ≤ count)
    (firstBound secondBound lastDifference penultimateValue lastValue : ℝ)
    (hfirstBound : 0 ≤ firstBound) (hsecondBound : 0 ≤ secondBound)
    (hlastDifference : ‖first (count - 1) - first (count - 2)‖ ≤ lastDifference)
    (hpenultimateValue : ‖first (count - 2)‖ ≤ penultimateValue)
    (hlastValue : ‖first (count - 1)‖ ≤ lastValue)
    (hsecondNorm : ∀ index, ‖second index‖ ≤ 1)
    (hfirstInterior : ∀ index, 0 < index → index < count →
      ‖second index - second (index - 1)‖ ≤ firstBound)
    (hsecondInterior : ∀ index, 2 ≤ index → index < count →
      ‖second index - 2 * second (index - 1) + second (index - 2)‖ ≤ secondBound) :
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖) ≤
      (∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference first count index‖) +
      2 * firstBound *
        (∑ index ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference first count index‖) +
      secondBound * (∑ index ∈ Finset.range count, ‖first index‖) +
      (2 * lastDifference + 3 * penultimateValue + lastValue) := by
  have hzeroPaddedNorm : ∀ index,
      ‖zeroPaddedCoefficient second count index‖ ≤ 1 := by
    intro index
    exact norm_zeroPaddedCoefficient_le (by norm_num) hsecondNorm count index
  have hcross : ∀ index ∈ Finset.range (count + 2),
      2 * ‖zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index‖ *
            ‖zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index‖ ≤
        2 * firstBound *
          ‖zeroPaddedPreviousCoefficient first count index -
            zeroPaddedSecondPreviousCoefficient first count index‖ +
        (if index = count then 2 * lastDifference else 0) := by
    intro index hindex
    rw [Finset.mem_range] at hindex
    by_cases hzero : index = 0
    · subst index
      simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
        show (0 : ℕ) ≠ count by omega]
    · by_cases hone : index = 1
      · subst index
        rw [zeroPadded_shiftedFirstDifference_at_one first count (by omega)]
        rw [zeroPadded_firstDifference_eq_internal second count 1 (by omega) (by omega)]
        simp only [if_neg (show 1 ≠ count by omega)]
        have hsecondZero := hfirstInterior 1 (by omega) (by omega)
        have hnonneg := norm_nonneg (first 0)
        nlinarith
      · by_cases hright : index = count
        · subst index
          rw [zeroPadded_shiftedFirstDifference_at_count first count htwo,
            zeroPadded_firstDifference_at_count second count (by omega)]
          simp only [if_pos, norm_neg]
          have hb := hsecondNorm (count - 1)
          have ha := norm_nonneg (first (count - 1) - first (count - 2))
          nlinarith
        · by_cases hafter : index = count + 1
          · subst index
            rw [zeroPadded_firstDifference_at_count_add_one second count]
            simp only [norm_zero, mul_zero, if_neg (show count + 1 ≠ count by omega)]
            have hnorm := norm_nonneg
              (zeroPaddedPreviousCoefficient first count (count + 1) -
                zeroPaddedSecondPreviousCoefficient first count (count + 1))
            positivity
          · have hinterior : index < count := by omega
            rw [zeroPadded_firstDifference_eq_internal second count index (by omega) hinterior]
            have hb := hfirstInterior index (by omega) hinterior
            have ha := norm_nonneg
              (zeroPaddedPreviousCoefficient first count index -
                zeroPaddedSecondPreviousCoefficient first count index)
            simp [hright]
            nlinarith
  have hcurvature : ∀ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondPreviousCoefficient first count index‖ *
          ‖zeroPaddedSecondDifference second count index‖ ≤
        secondBound * ‖zeroPaddedSecondPreviousCoefficient first count index‖ +
          (if index = count then 3 * penultimateValue else
            if index = count + 1 then lastValue else 0) := by
    intro index hindex
    rw [Finset.mem_range] at hindex
    by_cases hsmall : index < 2
    · have hnotCount : index ≠ count := by omega
      have hnotAfter : index ≠ count + 1 := by omega
      simp [zeroPaddedSecondPreviousCoefficient, hsmall,
        hnotCount, hnotAfter]
    · by_cases hright : index = count
      · subst index
        rw [zeroPadded_secondDifference_at_count second count htwo]
        simp only [if_pos]
        have hb : ‖-2 * second (count - 1) + second (count - 2)‖ ≤ 3 := by
          calc
            ‖-2 * second (count - 1) + second (count - 2)‖ ≤
                ‖-2 * second (count - 1)‖ + ‖second (count - 2)‖ := norm_add_le _ _
            _ ≤ 2 * 1 + 1 := by
              rw [norm_mul, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num]
              gcongr
              · exact hsecondNorm (count - 1)
              · exact hsecondNorm (count - 2)
            _ = 3 := by norm_num
        have ha : ‖zeroPaddedSecondPreviousCoefficient first count count‖ ≤
            penultimateValue := by
          simpa [zeroPaddedSecondPreviousCoefficient, show ¬count < 2 by omega,
            zeroPaddedCoefficient, show count - 2 < count by omega] using hpenultimateValue
        have hnonneg := norm_nonneg
          (zeroPaddedSecondPreviousCoefficient first count count)
        nlinarith
      · by_cases hafter : index = count + 1
        · subst index
          rw [zeroPadded_secondDifference_at_count_add_one second count (by omega)]
          simp only [if_neg (show count + 1 ≠ count by omega), if_pos]
          have hb := hsecondNorm (count - 1)
          have ha : ‖zeroPaddedSecondPreviousCoefficient first count (count + 1)‖ ≤
              lastValue := by
            simpa [zeroPaddedSecondPreviousCoefficient,
              show ¬count + 1 < 2 by omega, zeroPaddedCoefficient,
              show count + 1 - 2 = count - 1 by omega,
              show count - 1 < count by omega] using hlastValue
          have hnonneg := norm_nonneg
            (zeroPaddedSecondPreviousCoefficient first count (count + 1))
          nlinarith
        · have hinterior : index < count := by omega
          rw [zeroPadded_secondDifference_eq_internal second count index (by omega) hinterior]
          have hb := hsecondInterior index (by omega) hinterior
          have ha := norm_nonneg
            (zeroPaddedSecondPreviousCoefficient first count index)
          simp [hright, hafter]
          nlinarith
  have hcurvatureError :
      (∑ index ∈ Finset.range (count + 2),
        (if index = count then 3 * penultimateValue else
          if index = count + 1 then lastValue else 0)) =
        3 * penultimateValue + lastValue := by
    have hsplit :
        (∑ index ∈ Finset.range (count + 2),
          (if index = count then 3 * penultimateValue else
            if index = count + 1 then lastValue else 0)) =
          (∑ index ∈ Finset.range (count + 2),
            (if index = count then 3 * penultimateValue else 0)) +
          ∑ index ∈ Finset.range (count + 2),
            (if index = count + 1 then lastValue else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro index _hindex
      by_cases hcount : index = count
      · subst index
        simp
      · simp [hcount]
    rw [hsplit]
    simp
  calc
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖) ≤
      ∑ index ∈ Finset.range (count + 2),
        (‖zeroPaddedSecondDifference first count index‖ +
          2 * firstBound *
            ‖zeroPaddedPreviousCoefficient first count index -
              zeroPaddedSecondPreviousCoefficient first count index‖ +
          secondBound * ‖zeroPaddedSecondPreviousCoefficient first count index‖ +
          (if index = count then 2 * lastDifference else 0) +
          (if index = count then 3 * penultimateValue else
            if index = count + 1 then lastValue else 0)) := by
      apply Finset.sum_le_sum
      intro index hindex
      refine (norm_zeroPaddedSecondDifference_mul_le first second count index).trans ?_
      have hzero := hzeroPaddedNorm index
      have hcrossIndex := hcross index hindex
      have hcurvatureIndex := hcurvature index hindex
      have hfirstNonneg := norm_nonneg (zeroPaddedSecondDifference first count index)
      nlinarith
    _ =
      (∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference first count index‖) +
      2 * firstBound *
        (∑ index ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference first count index‖) +
      secondBound * (∑ index ∈ Finset.range count, ‖first index‖) +
      (2 * lastDifference + 3 * penultimateValue + lastValue) := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum,
        sum_norm_zeroPaddedPrevious_sub_secondPrevious,
        ← Finset.mul_sum,
        sum_norm_zeroPaddedSecondPreviousCoefficient,
        hcurvatureError]
      simp
      ring

/-! ## The actual transverse-annular Hodge slice -/

/-- The reindexed Hodge slice at the next index is the unit coordinate increment of the current
frequency. -/
theorem hodgeMultiplierSlice_succ
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    hodgeMultiplierSlice radius axis base component coordinate input (index + 1) =
      hodgeJacobianMultiplierEntry
        (incrementFrequencyCoordinate axis
          (replaceFrequencyCoordinate axis base
            (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index)))
        component coordinate input := by
  dsimp [hodgeMultiplierSlice]
  rw [replaceFrequencyCoordinate_centered_succ]

/-- The reindexed Hodge slice two indices later is the twice-incremented current frequency. -/
theorem hodgeMultiplierSlice_add_two
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    hodgeMultiplierSlice radius axis base component coordinate input (index + 2) =
      hodgeJacobianMultiplierEntry
        (twiceIncrementFrequencyCoordinate axis
          (replaceFrequencyCoordinate axis base
            (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index)))
        component coordinate input := by
  dsimp [hodgeMultiplierSlice]
  rw [replaceFrequencyCoordinate_centered_add_two]

/-- Every raw reindexed Hodge entry has magnitude at most one. -/
theorem norm_hodgeMultiplierSlice_le_one
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    ‖hodgeMultiplierSlice radius axis base component coordinate input index‖ ≤ 1 := by
  exact norm_hodgeJacobianMultiplierEntry_le_one _ component coordinate input

/-- Along a line with one transverse coordinate outside the inner cube, every genuine internal
first Hodge stencil receives the reciprocal-scale localized estimate. -/
theorem norm_hodgeMultiplierSlice_sub_previous_le_of_transverse
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∃ other : Fin 3,
      other ≠ axis ∧ radius + 2 ≤ (base other).natAbs)
    (index : ℕ) (hpositive : 0 < index) (hindex : index < 4 * radius + 7) :
    ‖hodgeMultiplierSlice radius axis base component coordinate input index -
        hodgeMultiplierSlice radius axis base component coordinate input (index - 1)‖ ≤
      8 / (radius + 2 : ℝ) := by
  let firstFrequency := replaceFrequencyCoordinate axis base
    (centeredFrequency (valleePoussinOuterRadius (radius + 1)) (index - 1))
  have hindexEq : index = (index - 1) + 1 := by omega
  have hfirstOuter : firstFrequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)) :=
    replaceFrequencyCoordinate_centered_mem_outer radius (index - 1) axis base
      hbaseOuter (by omega)
  have hnextOuter : incrementFrequencyCoordinate axis firstFrequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)) := by
    rw [← replaceFrequencyCoordinate_centered_succ]
    rw [← hindexEq]
    exact replaceFrequencyCoordinate_centered_mem_outer radius index axis base hbaseOuter hindex
  have hfirstInner : firstFrequency ∉ frequencyCube (radius + 1) :=
    replaceFrequencyCoordinate_not_mem_inner_of_transverse radius axis base _ htransverse
  have hnextInner : incrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_succ]
    exact replaceFrequencyCoordinate_not_mem_inner_of_transverse radius axis base _ htransverse
  have hnextEntry :
      hodgeMultiplierSlice radius axis base component coordinate input index =
        hodgeJacobianMultiplierEntry
          (incrementFrequencyCoordinate axis firstFrequency) component coordinate input := by
    rw [hindexEq, hodgeMultiplierSlice_succ]
  have hfirstEntry :
      hodgeMultiplierSlice radius axis base component coordinate input (index - 1) =
        hodgeJacobianMultiplierEntry firstFrequency component coordinate input := by
    rfl
  rw [hnextEntry, hfirstEntry]
  change ‖hodgeJacobianMultiplierEntry
      (incrementFrequencyCoordinate axis firstFrequency) component coordinate input -
    hodgeJacobianMultiplierEntry firstFrequency component coordinate input‖ ≤ _
  exact norm_hodgeJacobianMultiplierEntry_increment_sub_le_eight_div
    radius firstFrequency axis component coordinate input
    hfirstOuter hfirstInner hnextOuter hnextInner

/-- The analogous internal second Hodge stencil has reciprocal-square curvature. -/
theorem norm_hodgeMultiplierSlice_secondDifference_le_of_transverse
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∃ other : Fin 3,
      other ≠ axis ∧ radius + 2 ≤ (base other).natAbs)
    (index : ℕ) (htwo : 2 ≤ index) (hindex : index < 4 * radius + 7) :
    ‖hodgeMultiplierSlice radius axis base component coordinate input index -
        2 * hodgeMultiplierSlice radius axis base component coordinate input (index - 1) +
        hodgeMultiplierSlice radius axis base component coordinate input (index - 2)‖ ≤
      442 / (radius + 2 : ℝ) ^ 2 := by
  let firstFrequency := replaceFrequencyCoordinate axis base
    (centeredFrequency (valleePoussinOuterRadius (radius + 1)) (index - 2))
  have hindexEq : index = (index - 2) + 2 := by omega
  have hmiddleEq : index - 1 = (index - 2) + 1 := by omega
  have hfirstOuter : firstFrequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)) :=
    replaceFrequencyCoordinate_centered_mem_outer radius (index - 2) axis base
      hbaseOuter (by omega)
  have hfirstInner : firstFrequency ∉ frequencyCube (radius + 1) :=
    replaceFrequencyCoordinate_not_mem_inner_of_transverse radius axis base _ htransverse
  have hmiddleInner : incrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_succ]
    exact replaceFrequencyCoordinate_not_mem_inner_of_transverse radius axis base _ htransverse
  have hlastInner : twiceIncrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_add_two]
    exact replaceFrequencyCoordinate_not_mem_inner_of_transverse radius axis base _ htransverse
  have hlastEntry :
      hodgeMultiplierSlice radius axis base component coordinate input index =
        hodgeJacobianMultiplierEntry
          (twiceIncrementFrequencyCoordinate axis firstFrequency)
            component coordinate input := by
    rw [hindexEq, hodgeMultiplierSlice_add_two]
  have hmiddleEntry :
      hodgeMultiplierSlice radius axis base component coordinate input (index - 1) =
        hodgeJacobianMultiplierEntry
          (incrementFrequencyCoordinate axis firstFrequency)
            component coordinate input := by
    rw [hmiddleEq, hodgeMultiplierSlice_succ]
  have hfirstEntry :
      hodgeMultiplierSlice radius axis base component coordinate input (index - 2) =
        hodgeJacobianMultiplierEntry firstFrequency component coordinate input := by
    rfl
  rw [hlastEntry, hmiddleEntry, hfirstEntry]
  change ‖hodgeJacobianMultiplierEntry
      (twiceIncrementFrequencyCoordinate axis firstFrequency) component coordinate input -
    2 * hodgeJacobianMultiplierEntry
      (incrementFrequencyCoordinate axis firstFrequency) component coordinate input +
    hodgeJacobianMultiplierEntry firstFrequency component coordinate input‖ ≤ _
  exact norm_hodgeJacobianMultiplierEntry_secondDifference_le_442
    radius axis firstFrequency component coordinate input hfirstOuter
      hfirstInner hmiddleInner hlastInner

/-- The genuine annular coefficient slice is exactly the product chart used by the
boundary-resolved theorem. -/
theorem adjacentTensorSlice_mul_hodgeMultiplierSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    adjacentTensorSlice radius axis base index *
        hodgeMultiplierSlice radius axis base component coordinate input index =
      annularHodgeCoefficientSlice radius axis base component coordinate input index := by
  rw [annularHodgeCoefficientSlice_eq_weight_mul_hodge,
    adjacentTensorSlice_eq_actual]
  rfl

/-- **First complete reciprocal one-axis variation theorem.**  If a transverse coordinate keeps
the whole line outside the cancelled inner cube, the actual zero-padded annular Hodge coefficient
has total second variation bounded by an explicit `O(radius⁻¹)` expression.  The returned bound
retains three explicit endpoint terms from the zero-padded product estimate. -/
theorem sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∃ other : Fin 3,
      other ≠ axis ∧ radius + 2 ≤ (base other).natAbs) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      8 / (radius + 1 : ℝ) +
        2 * (8 / (radius + 2 : ℝ)) * 8 +
        (442 / (radius + 2 : ℝ) ^ 2) * (4 * radius + 7) +
        (2 * (3 / (radius + 2 : ℝ)) +
          3 * (2 / (radius + 2 : ℝ)) + 1 / (radius + 2 : ℝ)) := by
  let first := adjacentTensorSlice radius axis base
  let second := hodgeMultiplierSlice radius axis base component coordinate input
  have hproduct : (fun position ↦ first position * second position) =
      annularHodgeCoefficientSlice radius axis base component coordinate input := by
    funext index
    exact adjacentTensorSlice_mul_hodgeMultiplierSlice
      radius axis base component coordinate input index
  have hgeneric := sum_norm_zeroPaddedSecondDifference_mul_le_of_internal
    first second (4 * radius + 7) (by omega)
    (8 / (radius + 2 : ℝ)) (442 / (radius + 2 : ℝ) ^ 2)
    (3 / (radius + 2 : ℝ)) (2 / (radius + 2 : ℝ)) (1 / (radius + 2 : ℝ))
    (by positivity) (by positivity)
    (by
      simpa [first] using
        norm_adjacentTensorSlice_terminalDifference_le radius axis base)
    (by
      simpa [first] using norm_adjacentTensorSlice_penultimate_le radius axis base)
    (by
      simpa [first] using norm_adjacentTensorSlice_terminal_le radius axis base)
    (fun index ↦ norm_hodgeMultiplierSlice_le_one
      radius axis base component coordinate input index)
    (fun index hpositive hindex ↦
      norm_hodgeMultiplierSlice_sub_previous_le_of_transverse
        radius axis base component coordinate input hbaseOuter htransverse
          index hpositive hindex)
    (fun index htwo hindex ↦
      norm_hodgeMultiplierSlice_secondDifference_le_of_transverse
        radius axis base component coordinate input hbaseOuter htransverse
          index htwo hindex)
  rw [hproduct] at hgeneric
  refine hgeneric.trans ?_
  have hsecondVariation :=
    sum_norm_zeroPaddedSecondDifference_adjacentTensorSlice_le radius axis base
  have hfirstVariation :=
    sum_norm_zeroPaddedBackwardDifference_adjacentTensorSlice_le_eight radius axis base
  have hmass := sum_norm_adjacentTensorSlice_le radius axis base
  dsimp [first] at hsecondVariation hfirstVariation hmass ⊢
  gcongr

/-- A single reciprocal-scale constant exposing the preceding theorem's asymptotic content. -/
theorem sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1917
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∃ other : Fin 3,
      other ≠ axis ∧ radius + 2 ≤ (base other).natAbs) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      1917 / (radius + 1 : ℝ) := by
  refine (sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse
    radius axis base component coordinate input hbaseOuter htransverse).trans ?_
  have hfirst : 0 < (radius + 1 : ℝ) := by positivity
  have hsecond : 0 < (radius + 2 : ℝ) := by positivity
  field_simp [hfirst.ne', hsecond.ne']
  nlinarith [show (0 : ℝ) ≤ radius by positivity]

section Audit

#print axioms sum_norm_zeroPaddedBackwardDifference_adjacentTensorSlice_le_eight
#print axioms sum_norm_zeroPaddedSecondDifference_mul_le_of_internal
#print axioms replaceFrequencyCoordinate_centered_mem_outer
#print axioms norm_hodgeMultiplierSlice_sub_previous_le_of_transverse
#print axioms norm_hodgeMultiplierSlice_secondDifference_le_of_transverse
#print axioms sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse
#print axioms sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1917

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeStencilSum
