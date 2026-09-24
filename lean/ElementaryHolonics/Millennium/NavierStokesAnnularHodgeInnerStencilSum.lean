import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeStencilSum

/-!
# Transverse-inner annular Hodge stencil closure

**[proved-derived]** This owner closes the coordinate lines whose two transverse frequencies lie
in the inner plateau.  Every wholly inner stencil cancels exactly.  The only remaining active
inner-boundary stencils are the four addressed indices `r+2`, `r+3`, `3r+5`, and `3r+6`; their
actual coefficient curvature is bounded directly by the reciprocal-scale taper, never by their
cardinality.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeStencilSum

/-! ## A pointwise-error summation receiver -/

/-- Summing a pointwise zero-padded product estimate separates the exact scalar second variation,
shifted first variation, raw mass, and a retained addressed error population. -/
theorem sum_norm_zeroPaddedSecondDifference_mul_le_of_pointwiseError
    (first second : ℕ → ℂ) (count : ℕ)
    (firstBound secondBound : ℝ) (error : ℕ → ℝ)
    (hpoint : ∀ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖ ≤
        ‖zeroPaddedSecondDifference first count index‖ +
          2 * firstBound *
            ‖zeroPaddedPreviousCoefficient first count index -
              zeroPaddedSecondPreviousCoefficient first count index‖ +
          secondBound * ‖zeroPaddedSecondPreviousCoefficient first count index‖ +
          error index) :
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖) ≤
      (∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference first count index‖) +
      2 * firstBound *
        (∑ index ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference first count index‖) +
      secondBound * (∑ index ∈ Finset.range count, ‖first index‖) +
      ∑ index ∈ Finset.range (count + 2), error index := by
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
          error index) := Finset.sum_le_sum hpoint
    _ =
      (∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference first count index‖) +
      2 * firstBound *
        (∑ index ∈ Finset.range (count + 1),
          ‖zeroPaddedBackwardDifference first count index‖) +
      secondBound * (∑ index ∈ Finset.range count, ‖first index‖) +
      ∑ index ∈ Finset.range (count + 2), error index := by
      simp_rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum,
        sum_norm_zeroPaddedPrevious_sub_secondPrevious,
        ← Finset.mul_sum,
        sum_norm_zeroPaddedSecondPreviousCoefficient]

/-! ## Scalar taper near the inner boundary -/

/-- Pointwise first variation of the next scalar chart in the common aperture. -/
theorem norm_zeroPaddedBackwardDifference_nextCoordinateSlice_le
    (radius index : ℕ) :
    ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ ≤
      1 / (radius + 2 : ℝ) := by
  have hchart : nextCoordinateSliceInAdjacentAperture radius =
      centeredValleePoussinProfile (radius + 1) := by
    funext position
    exact (centeredCoordinateValleePoussinSlice_eq_profile (radius + 1) position)
  rw [hchart]
  convert norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le
    (radius + 1) index using 1 <;> push_cast <;> ring_nf

/-- Pointwise first variation of the transported base scalar chart. -/
theorem norm_zeroPaddedBackwardDifference_baseCoordinateSlice_le
    (radius index : ℕ) :
    ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ ≤
      1 / (radius + 1 : ℝ) := by
  rw [show baseCoordinateSliceInAdjacentAperture radius =
      twoSidedPadTwo (centeredValleePoussinProfile radius) (4 * radius + 3) by
        funext position
        exact baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo radius position]
  rw [zeroPaddedBackwardDifference_twoSidedPadTwo]
  unfold twoSidedPadTwo
  split_ifs with hinterior
  · exact norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le
      radius (index - 2)
  · simpa using (show 0 ≤ 1 / (radius + 1 : ℝ) by positivity)

/-- Every adjacent scalar step costs at most two reciprocal base-scale units. -/
theorem norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_two_div
    (radius index : ℕ) :
    ‖zeroPaddedBackwardDifference (adjacentCoordinateSlice radius)
        (4 * radius + 7) index‖ ≤
      2 / (radius + 1 : ℝ) := by
  rw [show zeroPaddedBackwardDifference (adjacentCoordinateSlice radius)
      (4 * radius + 7) index =
      zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index -
        zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index by
        exact zeroPaddedBackwardDifference_sub _ _ _ _]
  calc
    ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index -
        zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ ≤
      ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ +
        ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ := norm_sub_le _ _
    _ ≤ 1 / (radius + 2 : ℝ) + 1 / (radius + 1 : ℝ) :=
      add_le_add
        (norm_zeroPaddedBackwardDifference_nextCoordinateSlice_le radius index)
        (norm_zeroPaddedBackwardDifference_baseCoordinateSlice_le radius index)
    _ ≤ 2 / (radius + 1 : ℝ) := by
      have hscale : (1 : ℝ) / (radius + 2 : ℝ) ≤ 1 / (radius + 1 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
      calc
        1 / (radius + 2 : ℝ) + 1 / (radius + 1 : ℝ) ≤
            1 / (radius + 1 : ℝ) + 1 / (radius + 1 : ℝ) :=
          add_le_add hscale le_rfl
        _ = 2 / (radius + 1 : ℝ) := by ring

/-! ## Transverse plateau reduction -/

/-- A transverse complement is exactly one when every retained coordinate lies in the scalar
plateau. -/
theorem tensorCoordinateComplement_eq_one_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    tensorCoordinateComplement radius axis base = 1 := by
  unfold tensorCoordinateComplement
  apply Finset.prod_eq_one
  intro other hother
  have hne : other ≠ axis := Finset.ne_of_mem_erase hother
  exact coordinateValleePoussinWeight_eq_one radius (htransverse other hne)

/-- On a transverse-inner line, the actual adjacent tensor slice reduces to its one-dimensional
adjacent scalar taper. -/
theorem adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1)
    (index : ℕ) :
    adjacentTensorSlice radius axis base index = adjacentCoordinateSlice radius index := by
  rw [adjacentTensorSlice, nextTensorSliceInAdjacentAperture_eq,
    baseTensorSliceInAdjacentAperture_eq,
    tensorCoordinateComplement_eq_one_of_transverse_inner radius axis base htransverse,
    tensorCoordinateComplement_eq_one_of_transverse_inner (radius + 1) axis base
      (fun other hother ↦ (htransverse other hother).trans (by omega))]
  simp [adjacentCoordinateSlice]

/-- The active-coordinate plateau endpoints are exact zeros of the adjacent scalar taper. -/
theorem adjacentCoordinateSlice_eq_zero_of_inner_index
    (radius index : ℕ) (hlower : radius + 2 ≤ index)
    (hupper : index ≤ 3 * radius + 4) :
    adjacentCoordinateSlice radius index = 0 := by
  let frequency := centeredFrequency (valleePoussinOuterRadius (radius + 1)) index
  have hfrequency : frequency.natAbs ≤ radius + 1 := by
    rw [natAbs_le_iff_bounds]
    unfold frequency centeredFrequency valleePoussinOuterRadius
    constructor <;> omega
  change ((coordinateValleePoussinWeight (radius + 1) frequency : ℂ) -
    (coordinateValleePoussinWeight radius frequency : ℂ)) = 0
  rw [coordinateValleePoussinWeight_eq_one (radius + 1) (by omega),
    coordinateValleePoussinWeight_eq_one radius hfrequency]
  ring_nf

/-- The genuine tensor slice is zero on the active plateau of a transverse-inner line. -/
theorem adjacentTensorSlice_eq_zero_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1)
    (index : ℕ) (hlower : radius + 2 ≤ index)
    (hupper : index ≤ 3 * radius + 4) :
    adjacentTensorSlice radius axis base index = 0 := by
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse]
  exact adjacentCoordinateSlice_eq_zero_of_inner_index radius index hlower hupper

/-- Every actual annular Hodge slice coefficient is bounded by its genuine scalar tensor factor. -/
theorem norm_annularHodgeCoefficientSlice_le_tensorSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) (index : ℕ) :
    ‖annularHodgeCoefficientSlice radius axis base component coordinate input index‖ ≤
      ‖adjacentTensorSlice radius axis base index‖ := by
  rw [← adjacentTensorSlice_mul_hodgeMultiplierSlice,
    norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_hodgeMultiplierSlice_le_one radius axis base component coordinate input index)

/-! ## The four addressed inner-boundary stencils -/

/-- The tensor coefficient immediately left of the active plateau is reciprocal-scale. -/
theorem norm_adjacentTensorSlice_left_previous_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖adjacentTensorSlice radius axis base (radius + 1)‖ ≤
      2 / (radius + 1 : ℝ) := by
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse]
  have hvariation :=
    norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_two_div
      radius (radius + 2)
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPadded_firstDifference_eq_internal
      (adjacentCoordinateSlice radius) (4 * radius + 7) (radius + 2)
      (by omega) (by omega),
    adjacentCoordinateSlice_eq_zero_of_inner_index radius (radius + 2)
      (by omega) (by omega), zero_sub, norm_neg] at hvariation
  simpa only [show radius + 2 - 1 = radius + 1 by omega] using hvariation

/-- The next coefficient to the left costs at most two additional scalar steps. -/
theorem norm_adjacentTensorSlice_left_secondPrevious_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖adjacentTensorSlice radius axis base radius‖ ≤
      4 / (radius + 1 : ℝ) := by
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse]
  have hstep :=
    norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_two_div
      radius (radius + 1)
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPadded_firstDifference_eq_internal
      (adjacentCoordinateSlice radius) (4 * radius + 7) (radius + 1)
      (by omega) (by omega)] at hstep
  have hprevious := norm_adjacentTensorSlice_left_previous_le
    radius axis base htransverse
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse] at hprevious
  calc
    ‖adjacentCoordinateSlice radius radius‖ =
        ‖adjacentCoordinateSlice radius (radius + 1) -
            (adjacentCoordinateSlice radius (radius + 1) -
              adjacentCoordinateSlice radius radius)‖ := by ring_nf
    _ ≤ ‖adjacentCoordinateSlice radius (radius + 1)‖ +
        ‖adjacentCoordinateSlice radius (radius + 1) -
          adjacentCoordinateSlice radius radius‖ := norm_sub_le _ _
    _ ≤ 2 / (radius + 1 : ℝ) + 2 / (radius + 1 : ℝ) :=
      add_le_add hprevious (by
        simpa only [show radius + 1 - 1 = radius by omega] using hstep)
    _ = 4 / (radius + 1 : ℝ) := by ring

/-- The tensor coefficient immediately right of the active plateau is reciprocal-scale. -/
theorem norm_adjacentTensorSlice_right_next_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖adjacentTensorSlice radius axis base (3 * radius + 5)‖ ≤
      2 / (radius + 1 : ℝ) := by
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse]
  have hvariation :=
    norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_two_div
      radius (3 * radius + 5)
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPadded_firstDifference_eq_internal
      (adjacentCoordinateSlice radius) (4 * radius + 7) (3 * radius + 5)
      (by omega) (by omega),
    show 3 * radius + 5 - 1 = 3 * radius + 4 by omega,
    adjacentCoordinateSlice_eq_zero_of_inner_index radius (3 * radius + 4)
      (by omega) (by omega)] at hvariation
  simpa only [sub_zero] using hvariation

/-- The second coefficient to the right costs at most two additional scalar steps. -/
theorem norm_adjacentTensorSlice_right_afterNext_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖adjacentTensorSlice radius axis base (3 * radius + 6)‖ ≤
      4 / (radius + 1 : ℝ) := by
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse]
  have hstep :=
    norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_two_div
      radius (3 * radius + 6)
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPadded_firstDifference_eq_internal
      (adjacentCoordinateSlice radius) (4 * radius + 7) (3 * radius + 6)
      (by omega) (by omega)] at hstep
  have hprevious := norm_adjacentTensorSlice_right_next_le
    radius axis base htransverse
  rw [adjacentTensorSlice_eq_adjacentCoordinateSlice_of_transverse_inner
    radius axis base htransverse] at hprevious
  calc
    ‖adjacentCoordinateSlice radius (3 * radius + 6)‖ =
        ‖(adjacentCoordinateSlice radius (3 * radius + 6) -
            adjacentCoordinateSlice radius (3 * radius + 5)) +
          adjacentCoordinateSlice radius (3 * radius + 5)‖ := by ring_nf
    _ ≤ ‖adjacentCoordinateSlice radius (3 * radius + 6) -
          adjacentCoordinateSlice radius (3 * radius + 5)‖ +
        ‖adjacentCoordinateSlice radius (3 * radius + 5)‖ := norm_add_le _ _
    _ ≤ 2 / (radius + 1 : ℝ) + 2 / (radius + 1 : ℝ) :=
      add_le_add (by
        simpa only [show 3 * radius + 6 - 1 = 3 * radius + 5 by omega] using hstep)
        hprevious
    _ = 4 / (radius + 1 : ℝ) := by ring

/-- Actual coefficient cancellation throughout the active plateau on a transverse-inner line. -/
theorem annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1)
    (index : ℕ) (hlower : radius + 2 ≤ index)
    (hupper : index ≤ 3 * radius + 4) :
    annularHodgeCoefficientSlice radius axis base component coordinate input index = 0 := by
  rw [← adjacentTensorSlice_mul_hodgeMultiplierSlice,
    adjacentTensorSlice_eq_zero_of_transverse_inner radius axis base htransverse
      index hlower hupper, zero_mul]

/-- The left entry stencil contributes at most eight reciprocal scale units. -/
theorem norm_annularHodgeCoefficientSlice_secondDifference_leftEntry_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      (4 * radius + 7) (radius + 2)‖ ≤
      8 / (radius + 1 : ℝ) := by
  rw [zeroPadded_secondDifference_eq_internal _ _ _ (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (radius + 2)
        (by omega) (by omega)]
  have hprevious := norm_annularHodgeCoefficientSlice_le_tensorSlice
    radius axis base component coordinate input (radius + 1)
  have hsecondPrevious := norm_annularHodgeCoefficientSlice_le_tensorSlice
    radius axis base component coordinate input radius
  have htensorPrevious := norm_adjacentTensorSlice_left_previous_le
    radius axis base htransverse
  have htensorSecondPrevious := norm_adjacentTensorSlice_left_secondPrevious_le
    radius axis base htransverse
  have hpreviousBound := hprevious.trans htensorPrevious
  have hsecondPreviousBound := hsecondPrevious.trans htensorSecondPrevious
  simp only [zero_sub]
  calc
    ‖-(2 * annularHodgeCoefficientSlice radius axis base component coordinate input
        (radius + 2 - 1)) +
      annularHodgeCoefficientSlice radius axis base component coordinate input
        (radius + 2 - 2)‖ ≤
      2 * ‖annularHodgeCoefficientSlice radius axis base component coordinate input
          (radius + 1)‖ +
        ‖annularHodgeCoefficientSlice radius axis base component coordinate input radius‖ := by
      rw [show radius + 2 - 1 = radius + 1 by omega,
        show radius + 2 - 2 = radius by omega]
      calc
        ‖-(2 * annularHodgeCoefficientSlice radius axis base component coordinate input
            (radius + 1)) +
          annularHodgeCoefficientSlice radius axis base component coordinate input radius‖ ≤
          ‖-(2 * annularHodgeCoefficientSlice radius axis base component coordinate input
            (radius + 1))‖ +
          ‖annularHodgeCoefficientSlice radius axis base component coordinate input radius‖ :=
            norm_add_le _ _
        _ = 2 * ‖annularHodgeCoefficientSlice radius axis base component coordinate input
            (radius + 1)‖ +
          ‖annularHodgeCoefficientSlice radius axis base component coordinate input radius‖ := by
            rw [norm_neg, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    _ ≤ 2 * (2 / (radius + 1 : ℝ)) + 4 / (radius + 1 : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpreviousBound (by norm_num))
        hsecondPreviousBound
    _ = 8 / (radius + 1 : ℝ) := by ring

/-- The next left stencil retains only its twice-previous reciprocal-scale coefficient. -/
theorem norm_annularHodgeCoefficientSlice_secondDifference_leftExit_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      (4 * radius + 7) (radius + 3)‖ ≤
      2 / (radius + 1 : ℝ) := by
  rw [zeroPadded_secondDifference_eq_internal _ _ _ (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (radius + 3)
        (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (radius + 3 - 1)
        (by omega) (by omega)]
  simpa only [mul_zero, sub_zero, zero_add,
    show radius + 3 - 2 = radius + 1 by omega] using
    (norm_annularHodgeCoefficientSlice_le_tensorSlice
      radius axis base component coordinate input (radius + 1)).trans
        (norm_adjacentTensorSlice_left_previous_le radius axis base htransverse)

/-- The first right exit stencil retains only its new reciprocal-scale coefficient. -/
theorem norm_annularHodgeCoefficientSlice_secondDifference_rightEntry_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      (4 * radius + 7) (3 * radius + 5)‖ ≤
      2 / (radius + 1 : ℝ) := by
  rw [zeroPadded_secondDifference_eq_internal _ _ _ (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (3 * radius + 5 - 1)
        (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (3 * radius + 5 - 2)
        (by omega) (by omega)]
  simpa only [mul_zero, sub_zero, add_zero] using
    (norm_annularHodgeCoefficientSlice_le_tensorSlice
      radius axis base component coordinate input (3 * radius + 5)).trans
        (norm_adjacentTensorSlice_right_next_le radius axis base htransverse)

/-- The final right exit stencil costs eight reciprocal scale units. -/
theorem norm_annularHodgeCoefficientSlice_secondDifference_rightExit_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    ‖zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      (4 * radius + 7) (3 * radius + 6)‖ ≤
      8 / (radius + 1 : ℝ) := by
  rw [zeroPadded_secondDifference_eq_internal _ _ _ (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (3 * radius + 6 - 2)
        (by omega) (by omega)]
  have hcurrent := (norm_annularHodgeCoefficientSlice_le_tensorSlice
    radius axis base component coordinate input (3 * radius + 6)).trans
      (norm_adjacentTensorSlice_right_afterNext_le radius axis base htransverse)
  have hprevious := (norm_annularHodgeCoefficientSlice_le_tensorSlice
    radius axis base component coordinate input (3 * radius + 5)).trans
      (norm_adjacentTensorSlice_right_next_le radius axis base htransverse)
  calc
    ‖annularHodgeCoefficientSlice radius axis base component coordinate input
          (3 * radius + 6) -
        2 * annularHodgeCoefficientSlice radius axis base component coordinate input
          (3 * radius + 6 - 1) + 0‖ ≤
      ‖annularHodgeCoefficientSlice radius axis base component coordinate input
          (3 * radius + 6)‖ +
        2 * ‖annularHodgeCoefficientSlice radius axis base component coordinate input
          (3 * radius + 5)‖ := by
      rw [show 3 * radius + 6 - 1 = 3 * radius + 5 by omega, add_zero]
      calc
        ‖annularHodgeCoefficientSlice radius axis base component coordinate input
            (3 * radius + 6) -
          2 * annularHodgeCoefficientSlice radius axis base component coordinate input
            (3 * radius + 5)‖ ≤
          ‖annularHodgeCoefficientSlice radius axis base component coordinate input
            (3 * radius + 6)‖ +
          ‖2 * annularHodgeCoefficientSlice radius axis base component coordinate input
            (3 * radius + 5)‖ := norm_sub_le _ _
        _ = _ := by rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    _ ≤ 4 / (radius + 1 : ℝ) + 2 * (2 / (radius + 1 : ℝ)) := by
      gcongr
    _ = 8 / (radius + 1 : ℝ) := by ring

/-! ## Regular active-coordinate rational stencils -/

/-- An active index left of the plateau represents a frequency outside the inner cube. -/
theorem replaceFrequencyCoordinate_not_mem_inner_of_left_index
    (radius index : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (hindex : index ≤ radius + 1) :
    replaceFrequencyCoordinate axis base
        (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index) ∉
      frequencyCube (radius + 1) := by
  intro hinner
  have haxis := (mem_frequencyCube_iff (radius + 1) _).mp hinner axis
  simp only [replaceFrequencyCoordinate, Function.update_self] at haxis
  unfold centeredFrequency valleePoussinOuterRadius at haxis
  omega

/-- An active index right of the plateau likewise represents a frequency outside the inner cube. -/
theorem replaceFrequencyCoordinate_not_mem_inner_of_right_index
    (radius index : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (hindex : 3 * radius + 5 ≤ index) :
    replaceFrequencyCoordinate axis base
        (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index) ∉
      frequencyCube (radius + 1) := by
  intro hinner
  have haxis := (mem_frequencyCube_iff (radius + 1) _).mp hinner axis
  simp only [replaceFrequencyCoordinate, Function.update_self] at haxis
  unfold centeredFrequency valleePoussinOuterRadius at haxis
  omega

/-- First Hodge differences on regular left/right active stencils retain the localized bound. -/
theorem norm_hodgeMultiplierSlice_sub_previous_le_of_active_outside
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (index : ℕ) (hpositive : 0 < index) (hindex : index < 4 * radius + 7)
    (hactive : index ≤ radius + 1 ∨ 3 * radius + 6 ≤ index) :
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
    rw [← replaceFrequencyCoordinate_centered_succ, ← hindexEq]
    exact replaceFrequencyCoordinate_centered_mem_outer radius index axis base hbaseOuter hindex
  have hfirstInner : firstFrequency ∉ frequencyCube (radius + 1) := by
    rcases hactive with hleft | hright
    · exact replaceFrequencyCoordinate_not_mem_inner_of_left_index
        radius (index - 1) axis base (by omega)
    · exact replaceFrequencyCoordinate_not_mem_inner_of_right_index
        radius (index - 1) axis base (by omega)
  have hnextInner : incrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_succ, ← hindexEq]
    rcases hactive with hleft | hright
    · exact replaceFrequencyCoordinate_not_mem_inner_of_left_index
        radius index axis base hleft
    · exact replaceFrequencyCoordinate_not_mem_inner_of_right_index
        radius index axis base (by omega)
  have hnextEntry :
      hodgeMultiplierSlice radius axis base component coordinate input index =
        hodgeJacobianMultiplierEntry
          (incrementFrequencyCoordinate axis firstFrequency) component coordinate input := by
    rw [hindexEq, hodgeMultiplierSlice_succ]
  have hfirstEntry :
      hodgeMultiplierSlice radius axis base component coordinate input (index - 1) =
        hodgeJacobianMultiplierEntry firstFrequency component coordinate input := by rfl
  rw [hnextEntry, hfirstEntry]
  exact norm_hodgeJacobianMultiplierEntry_increment_sub_le_eight_div
    radius firstFrequency axis component coordinate input
      hfirstOuter hfirstInner hnextOuter hnextInner

/-- Second Hodge curvature on regular left/right active stencils is reciprocal-square. -/
theorem norm_hodgeMultiplierSlice_secondDifference_le_of_active_outside
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (index : ℕ) (htwo : 2 ≤ index) (hindex : index < 4 * radius + 7)
    (hactive : index ≤ radius + 1 ∨ 3 * radius + 7 ≤ index) :
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
  have hfirstInner : firstFrequency ∉ frequencyCube (radius + 1) := by
    rcases hactive with hleft | hright
    · exact replaceFrequencyCoordinate_not_mem_inner_of_left_index
        radius (index - 2) axis base (by omega)
    · exact replaceFrequencyCoordinate_not_mem_inner_of_right_index
        radius (index - 2) axis base (by omega)
  have hmiddleInner : incrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_succ, ← hmiddleEq]
    rcases hactive with hleft | hright
    · exact replaceFrequencyCoordinate_not_mem_inner_of_left_index
        radius (index - 1) axis base (by omega)
    · exact replaceFrequencyCoordinate_not_mem_inner_of_right_index
        radius (index - 1) axis base (by omega)
  have hlastInner : twiceIncrementFrequencyCoordinate axis firstFrequency ∉
      frequencyCube (radius + 1) := by
    rw [← replaceFrequencyCoordinate_centered_add_two, ← hindexEq]
    rcases hactive with hleft | hright
    · exact replaceFrequencyCoordinate_not_mem_inner_of_left_index
        radius index axis base hleft
    · exact replaceFrequencyCoordinate_not_mem_inner_of_right_index
        radius index axis base (by omega)
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
        hodgeJacobianMultiplierEntry firstFrequency component coordinate input := by rfl
  rw [hlastEntry, hmiddleEntry, hfirstEntry]
  exact norm_hodgeJacobianMultiplierEntry_secondDifference_le_442
    radius axis firstFrequency component coordinate input hfirstOuter
      hfirstInner hmiddleInner hlastInner

/-! ## Addressed error population -/

/-- The four inner-boundary stencils and two terminal aperture stencils, as six addressed
Kronecker populations. -/
def transverseInnerStencilError (radius index : ℕ) : ℝ :=
  (if index = radius + 2 then 8 / (radius + 1 : ℝ) else 0) +
  (if index = radius + 3 then 2 / (radius + 1 : ℝ) else 0) +
  (if index = 3 * radius + 5 then 2 / (radius + 1 : ℝ) else 0) +
  (if index = 3 * radius + 6 then 8 / (radius + 1 : ℝ) else 0) +
  (if index = 4 * radius + 7 then 12 / (radius + 2 : ℝ) else 0) +
  (if index = 4 * radius + 8 then 1 / (radius + 2 : ℝ) else 0)

theorem transverseInnerStencilError_nonneg (radius index : ℕ) :
    0 ≤ transverseInnerStencilError radius index := by
  unfold transverseInnerStencilError
  split_ifs <;> positivity

/-- The exact error mass is twenty inner-boundary units and thirteen aperture-boundary units. -/
theorem sum_transverseInnerStencilError (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      transverseInnerStencilError radius index) =
      20 / (radius + 1 : ℝ) + 13 / (radius + 2 : ℝ) := by
  unfold transverseInnerStencilError
  simp_rw [Finset.sum_add_distrib]
  simp
  rw [if_pos (show radius < 4 * radius + 7 by omega),
    if_pos (show radius < 4 * radius + 6 by omega),
    if_pos (show 3 * radius < 4 * radius + 4 by omega),
    if_pos (show 3 * radius < 4 * radius + 3 by omega)]
  ring

theorem transverseInnerStencilError_leftEntry (radius : ℕ) :
    transverseInnerStencilError radius (radius + 2) =
      8 / (radius + 1 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_pos rfl, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  ring

theorem transverseInnerStencilError_leftExit (radius : ℕ) :
    transverseInnerStencilError radius (radius + 3) =
      2 / (radius + 1 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  ring

theorem transverseInnerStencilError_rightEntry (radius : ℕ) :
    transverseInnerStencilError radius (3 * radius + 5) =
      2 / (radius + 1 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_neg (by omega), if_neg (by omega), if_pos rfl, if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]
  ring

theorem transverseInnerStencilError_rightExit (radius : ℕ) :
    transverseInnerStencilError radius (3 * radius + 6) =
      8 / (radius + 1 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl,
    if_neg (by omega), if_neg (by omega)]
  ring

theorem transverseInnerStencilError_terminal (radius : ℕ) :
    transverseInnerStencilError radius (4 * radius + 7) =
      12 / (radius + 2 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_pos rfl, if_neg (by omega)]
  ring

theorem transverseInnerStencilError_afterTerminal (radius : ℕ) :
    transverseInnerStencilError radius (4 * radius + 8) =
      1 / (radius + 2 : ℝ) := by
  unfold transverseInnerStencilError
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]
  ring

/-! ## Pointwise composition -/

/-- On every genuine three-point active stencil outside the plateau, the exact product rule
receives the localized rational bounds. -/
theorem norm_zeroPaddedSecondDifference_sliceProduct_le_of_active_outside
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (index : ℕ) (htwo : 2 ≤ index) (hindex : index < 4 * radius + 7)
    (hactive : index ≤ radius + 1 ∨ 3 * radius + 7 ≤ index) :
    ‖zeroPaddedSecondDifference
      (fun position ↦ adjacentTensorSlice radius axis base position *
        hodgeMultiplierSlice radius axis base component coordinate input position)
      (4 * radius + 7) index‖ ≤
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index‖ +
      2 * (8 / (radius + 2 : ℝ)) *
        ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index -
          zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index‖ +
      (442 / (radius + 2 : ℝ) ^ 2) *
        ‖zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index‖ := by
  let second := hodgeMultiplierSlice radius axis base component coordinate input
  have hzero : ‖zeroPaddedCoefficient second (4 * radius + 7) index‖ ≤ 1 := by
    rw [show zeroPaddedCoefficient second (4 * radius + 7) index = second index by
      simp [zeroPaddedCoefficient, hindex]]
    exact norm_hodgeMultiplierSlice_le_one radius axis base component coordinate input index
  have hfirst :
      ‖zeroPaddedCoefficient second (4 * radius + 7) index -
          zeroPaddedPreviousCoefficient second (4 * radius + 7) index‖ ≤
        8 / (radius + 2 : ℝ) := by
    rw [zeroPadded_firstDifference_eq_internal second (4 * radius + 7) index
      (by omega) hindex]
    exact norm_hodgeMultiplierSlice_sub_previous_le_of_active_outside
      radius axis base component coordinate input hbaseOuter index (by omega) hindex
        (by rcases hactive with hleft | hright <;> omega)
  have hsecond : ‖zeroPaddedSecondDifference second (4 * radius + 7) index‖ ≤
      442 / (radius + 2 : ℝ) ^ 2 := by
    rw [zeroPadded_secondDifference_eq_internal second (4 * radius + 7) index htwo hindex]
    exact norm_hodgeMultiplierSlice_secondDifference_le_of_active_outside
      radius axis base component coordinate input hbaseOuter index htwo hindex hactive
  refine (norm_zeroPaddedSecondDifference_mul_le
    (adjacentTensorSlice radius axis base) second (4 * radius + 7) index).trans ?_
  have hleading :
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index‖ *
          ‖zeroPaddedCoefficient second (4 * radius + 7) index‖ ≤
        ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index‖ := by
    simpa using mul_le_of_le_one_right (norm_nonneg _) hzero
  have hcross :
      2 * ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index -
          zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index‖ *
          ‖zeroPaddedCoefficient second (4 * radius + 7) index -
            zeroPaddedPreviousCoefficient second (4 * radius + 7) index‖ ≤
        2 * (8 / (radius + 2 : ℝ)) *
          ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
              (4 * radius + 7) index -
            zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
              (4 * radius + 7) index‖ := by
    have hscale : 0 ≤ (2 : ℝ) *
        ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index -
          zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index‖ :=
      mul_nonneg (by norm_num) (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hfirst hscale
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  have hcurvature :
      ‖zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index‖ *
          ‖zeroPaddedSecondDifference second (4 * radius + 7) index‖ ≤
        (442 / (radius + 2 : ℝ) ^ 2) *
          ‖zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) index‖ := by
    have := mul_le_mul_of_nonneg_left hsecond (norm_nonneg
      (zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index))
    simpa [mul_comm] using this
  exact add_le_add (add_le_add hleading hcross) hcurvature

/-- The initial aperture point has only the zeroth multiplier term. -/
theorem norm_zeroPaddedSecondDifference_sliceProduct_at_zero_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖zeroPaddedSecondDifference
      (fun position ↦ adjacentTensorSlice radius axis base position *
        hodgeMultiplierSlice radius axis base component coordinate input position)
      (4 * radius + 7) 0‖ ≤
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) 0‖ := by
  simp [zeroPaddedSecondDifference, zeroPaddedBackwardDifference,
    zeroPaddedCoefficient]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (norm_hodgeMultiplierSlice_le_one radius axis base component coordinate input 0)

/-- At index one the twice-previous scalar factor is zero, so only the localized first Hodge
difference is required. -/
theorem norm_zeroPaddedSecondDifference_sliceProduct_at_one_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1))) :
    ‖zeroPaddedSecondDifference
      (fun position ↦ adjacentTensorSlice radius axis base position *
        hodgeMultiplierSlice radius axis base component coordinate input position)
      (4 * radius + 7) 1‖ ≤
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) 1‖ +
      2 * (8 / (radius + 2 : ℝ)) *
        ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) 1 -
          zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) 1‖ +
      (442 / (radius + 2 : ℝ) ^ 2) *
        ‖zeroPaddedSecondPreviousCoefficient (adjacentTensorSlice radius axis base)
          (4 * radius + 7) 1‖ := by
  let second := hodgeMultiplierSlice radius axis base component coordinate input
  have hzero : ‖zeroPaddedCoefficient second (4 * radius + 7) 1‖ ≤ 1 := by
    rw [show zeroPaddedCoefficient second (4 * radius + 7) 1 = second 1 by
      simp [zeroPaddedCoefficient]]
    exact norm_hodgeMultiplierSlice_le_one radius axis base component coordinate input 1
  have hfirst :
      ‖zeroPaddedCoefficient second (4 * radius + 7) 1 -
          zeroPaddedPreviousCoefficient second (4 * radius + 7) 1‖ ≤
        8 / (radius + 2 : ℝ) := by
    rw [zeroPadded_firstDifference_eq_internal second (4 * radius + 7) 1
      (by omega) (by omega)]
    exact norm_hodgeMultiplierSlice_sub_previous_le_of_active_outside
      radius axis base component coordinate input hbaseOuter 1 (by omega) (by omega)
        (by left; omega)
  have hproduct := norm_zeroPaddedSecondDifference_mul_le
    (adjacentTensorSlice radius axis base) second (4 * radius + 7) 1
  simp [zeroPaddedSecondPreviousCoefficient] at hproduct ⊢
  refine hproduct.trans ?_
  have hleading :
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) 1‖ *
          ‖zeroPaddedCoefficient second (4 * radius + 7) 1‖ ≤
        ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) 1‖ := by
    simpa using mul_le_of_le_one_right (norm_nonneg _) hzero
  have hcross :
      2 * ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
          (4 * radius + 7) 1‖ *
          ‖zeroPaddedCoefficient second (4 * radius + 7) 1 -
            zeroPaddedPreviousCoefficient second (4 * radius + 7) 1‖ ≤
        2 * (8 / (radius + 2 : ℝ)) *
          ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
            (4 * radius + 7) 1‖ := by
    have hscale : 0 ≤ (2 : ℝ) *
        ‖zeroPaddedPreviousCoefficient (adjacentTensorSlice radius axis base)
          (4 * radius + 7) 1‖ :=
      mul_nonneg (by norm_num) (norm_nonneg _)
    have := mul_le_mul_of_nonneg_left hfirst hscale
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  exact add_le_add hleading hcross

/-- Every three-point stencil wholly in the active plateau vanishes exactly. -/
theorem zeroPaddedSecondDifference_annularHodgeCoefficientSlice_eq_zero_of_inner_stencil
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1)
    (index : ℕ) (hlower : radius + 4 ≤ index)
    (hupper : index ≤ 3 * radius + 4) :
    zeroPaddedSecondDifference
      (annularHodgeCoefficientSlice radius axis base component coordinate input)
      (4 * radius + 7) index = 0 := by
  rw [zeroPadded_secondDifference_eq_internal _ _ _ (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse index (by omega) hupper,
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (index - 1)
        (by omega) (by omega),
    annularHodgeCoefficientSlice_eq_zero_of_transverse_inner
      radius axis base component coordinate input htransverse (index - 2)
        (by omega) (by omega)]
  ring

/-- At the first point beyond the aperture the actual product curvature costs exactly the two
terminal taper residues bounded earlier. -/
theorem norm_zeroPaddedSecondDifference_sliceProduct_at_terminal_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖zeroPaddedSecondDifference
      (fun position ↦ adjacentTensorSlice radius axis base position *
        hodgeMultiplierSlice radius axis base component coordinate input position)
      (4 * radius + 7) (4 * radius + 7)‖ ≤
      12 / (radius + 2 : ℝ) := by
  let first := adjacentTensorSlice radius axis base
  let second := hodgeMultiplierSlice radius axis base component coordinate input
  have hproduct := norm_zeroPaddedSecondDifference_mul_le first second
    (4 * radius + 7) (4 * radius + 7)
  rw [zeroPaddedCoefficient, if_neg (show ¬4 * radius + 7 < 4 * radius + 7 by omega),
    norm_zero, mul_zero, zero_add] at hproduct
  rw [zeroPadded_shiftedFirstDifference_at_count first (4 * radius + 7) (by omega),
    zeroPadded_secondDifference_at_count second (4 * radius + 7) (by omega)] at hproduct
  simp only [zero_sub, norm_neg] at hproduct
  have hfirstDifference : ‖first (4 * radius + 7 - 1) -
      first (4 * radius + 7 - 2)‖ ≤ 3 / (radius + 2 : ℝ) := by
    simpa [first] using norm_adjacentTensorSlice_terminalDifference_le radius axis base
  have hpenultimate : ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7)
      (4 * radius + 7)‖ ≤ 2 / (radius + 2 : ℝ) := by
    simpa [first, zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient] using
      norm_adjacentTensorSlice_penultimate_le radius axis base
  have hlastSecond := norm_hodgeMultiplierSlice_le_one
    radius axis base component coordinate input (4 * radius + 6)
  have hpreviousSecond := norm_hodgeMultiplierSlice_le_one
    radius axis base component coordinate input (4 * radius + 5)
  have hlastSecondPadded :
      ‖zeroPaddedPreviousCoefficient second (4 * radius + 7) (4 * radius + 7)‖ ≤ 1 := by
    simpa [second, zeroPaddedPreviousCoefficient, zeroPaddedCoefficient,
      show (4 * radius + 7 : ℕ) ≠ 0 by omega,
      show 4 * radius + 7 - 1 < 4 * radius + 7 by omega,
      show 4 * radius + 7 - 1 = 4 * radius + 6 by omega] using hlastSecond
  refine hproduct.trans ?_
  have hcurvature :
      ‖-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2)‖ ≤ 3 := by
    calc
      ‖-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2)‖ ≤
          2 * ‖second (4 * radius + 6)‖ + ‖second (4 * radius + 5)‖ := by
        rw [show 4 * radius + 7 - 1 = 4 * radius + 6 by omega,
          show 4 * radius + 7 - 2 = 4 * radius + 5 by omega]
        calc
          ‖-2 * second (4 * radius + 6) + second (4 * radius + 5)‖ ≤
            ‖-2 * second (4 * radius + 6)‖ + ‖second (4 * radius + 5)‖ :=
              norm_add_le _ _
          _ = _ := by rw [norm_mul, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num]
      _ ≤ 2 * 1 + 1 := by gcongr
      _ = 3 := by norm_num
  have hfirstNonneg := norm_nonneg
    (first (4 * radius + 7 - 1) - first (4 * radius + 7 - 2))
  have hpenultimateNonneg := norm_nonneg
    (zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) (4 * radius + 7))
  have hlastSecondNonneg := norm_nonneg
    (zeroPaddedPreviousCoefficient second (4 * radius + 7) (4 * radius + 7))
  have hcurvatureNonneg := norm_nonneg
    (-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2))
  have hcrossTerm :
      2 * ‖first (4 * radius + 7 - 1) - first (4 * radius + 7 - 2)‖ *
          ‖zeroPaddedPreviousCoefficient second (4 * radius + 7)
            (4 * radius + 7)‖ ≤
        2 * (3 / (radius + 2 : ℝ)) * 1 := by
    calc
      2 * ‖first (4 * radius + 7 - 1) - first (4 * radius + 7 - 2)‖ *
          ‖zeroPaddedPreviousCoefficient second (4 * radius + 7)
            (4 * radius + 7)‖ ≤
        2 * (3 / (radius + 2 : ℝ)) *
          ‖zeroPaddedPreviousCoefficient second (4 * radius + 7)
            (4 * radius + 7)‖ := by gcongr
      _ ≤ 2 * (3 / (radius + 2 : ℝ)) * 1 := by gcongr
  have hcurvatureTerm :
      ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7)
          (4 * radius + 7)‖ *
          ‖-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2)‖ ≤
        (2 / (radius + 2 : ℝ)) * 3 := by
    calc
      ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7)
          (4 * radius + 7)‖ *
          ‖-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2)‖ ≤
        (2 / (radius + 2 : ℝ)) *
          ‖-2 * second (4 * radius + 7 - 1) + second (4 * radius + 7 - 2)‖ := by
            gcongr
      _ ≤ (2 / (radius + 2 : ℝ)) * 3 := by gcongr
  refine (add_le_add hcrossTerm hcurvatureTerm).trans ?_
  ring_nf
  exact le_rfl

/-- The final zero-padded stencil is the last actual coefficient and costs one reciprocal unit. -/
theorem norm_zeroPaddedSecondDifference_sliceProduct_after_terminal_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖zeroPaddedSecondDifference
      (fun position ↦ adjacentTensorSlice radius axis base position *
        hodgeMultiplierSlice radius axis base component coordinate input position)
      (4 * radius + 7) (4 * radius + 8)‖ ≤
      1 / (radius + 2 : ℝ) := by
  rw [zeroPadded_secondDifference_at_count_add_one _ (4 * radius + 7) (by omega)]
  rw [norm_mul]
  rw [show 4 * radius + 7 - 1 = 4 * radius + 6 by omega]
  calc
    ‖adjacentTensorSlice radius axis base (4 * radius + 6)‖ *
        ‖hodgeMultiplierSlice radius axis base component coordinate input
          (4 * radius + 6)‖ ≤
      ‖adjacentTensorSlice radius axis base (4 * radius + 6)‖ * 1 :=
        mul_le_mul_of_nonneg_left
          (norm_hodgeMultiplierSlice_le_one radius axis base component coordinate input
            (4 * radius + 6)) (norm_nonneg _)
    _ = ‖adjacentTensorSlice radius axis base (4 * radius + 6)‖ := by ring
    _ ≤ 1 / (radius + 2 : ℝ) :=
      norm_adjacentTensorSlice_terminal_le radius axis base

/-! ## Exhaustive transverse-inner line -/

/-- The transverse-inner line has reciprocal-scale total second variation.  The four inner faces
and two aperture faces remain visible in the final estimate rather than being charged per mode. -/
theorem sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      8 / (radius + 1 : ℝ) +
        2 * (8 / (radius + 2 : ℝ)) * 8 +
        (442 / (radius + 2 : ℝ) ^ 2) * (4 * radius + 7) +
        (20 / (radius + 1 : ℝ) + 13 / (radius + 2 : ℝ)) := by
  let first := adjacentTensorSlice radius axis base
  let second := hodgeMultiplierSlice radius axis base component coordinate input
  have hproduct : (fun position ↦ first position * second position) =
      annularHodgeCoefficientSlice radius axis base component coordinate input := by
    funext index
    exact adjacentTensorSlice_mul_hodgeMultiplierSlice
      radius axis base component coordinate input index
  have hcrossNonneg (index : ℕ) :
      0 ≤ 2 * (8 / (radius + 2 : ℝ)) *
        ‖zeroPaddedPreviousCoefficient first (4 * radius + 7) index -
          zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ := by
    positivity
  have hcurvatureNonneg (index : ℕ) :
      0 ≤ (442 / (radius + 2 : ℝ) ^ 2) *
        ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ := by
    positivity
  have hfromScalar (index : ℕ) :
      ‖zeroPaddedSecondDifference first (4 * radius + 7) index‖ ≤
        ‖zeroPaddedSecondDifference first (4 * radius + 7) index‖ +
          2 * (8 / (radius + 2 : ℝ)) *
            ‖zeroPaddedPreviousCoefficient first (4 * radius + 7) index -
              zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          (442 / (radius + 2 : ℝ) ^ 2) *
            ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          transverseInnerStencilError radius index := by
    have herrorNonneg := transverseInnerStencilError_nonneg radius index
    linarith [hcrossNonneg index, hcurvatureNonneg index]
  have hfromError (index : ℕ) :
      transverseInnerStencilError radius index ≤
        ‖zeroPaddedSecondDifference first (4 * radius + 7) index‖ +
          2 * (8 / (radius + 2 : ℝ)) *
            ‖zeroPaddedPreviousCoefficient first (4 * radius + 7) index -
              zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          (442 / (radius + 2 : ℝ) ^ 2) *
            ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          transverseInnerStencilError radius index := by
    have hscalarNonneg := norm_nonneg
      (zeroPaddedSecondDifference first (4 * radius + 7) index)
    linarith [hcrossNonneg index, hcurvatureNonneg index]
  have hfullNonneg (index : ℕ) :
      0 ≤ ‖zeroPaddedSecondDifference first (4 * radius + 7) index‖ +
          2 * (8 / (radius + 2 : ℝ)) *
            ‖zeroPaddedPreviousCoefficient first (4 * radius + 7) index -
              zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          (442 / (radius + 2 : ℝ) ^ 2) *
            ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          transverseInnerStencilError radius index := by
    have hscalarNonneg := norm_nonneg
      (zeroPaddedSecondDifference first (4 * radius + 7) index)
    have herrorNonneg := transverseInnerStencilError_nonneg radius index
    linarith [hcrossNonneg index, hcurvatureNonneg index]
  have hpoint : ∀ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) (4 * radius + 7) index‖ ≤
        ‖zeroPaddedSecondDifference first (4 * radius + 7) index‖ +
          2 * (8 / (radius + 2 : ℝ)) *
            ‖zeroPaddedPreviousCoefficient first (4 * radius + 7) index -
              zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          (442 / (radius + 2 : ℝ) ^ 2) *
            ‖zeroPaddedSecondPreviousCoefficient first (4 * radius + 7) index‖ +
          transverseInnerStencilError radius index := by
    intro index hindexRange
    rw [Finset.mem_range] at hindexRange
    by_cases hzero : index = 0
    · subst index
      have hbound := norm_zeroPaddedSecondDifference_sliceProduct_at_zero_le
        radius axis base component coordinate input
      dsimp [first, second] at hbound ⊢
      exact hbound.trans (hfromScalar 0)
    · by_cases hone : index = 1
      · subst index
        have hbound := norm_zeroPaddedSecondDifference_sliceProduct_at_one_le
          radius axis base component coordinate input hbaseOuter
        dsimp [first, second] at hbound ⊢
        exact hbound.trans
          (le_add_of_nonneg_right (transverseInnerStencilError_nonneg radius 1))
      · by_cases hterminal : index = 4 * radius + 7
        · subst index
          have hbound := norm_zeroPaddedSecondDifference_sliceProduct_at_terminal_le
            radius axis base component coordinate input
          dsimp [first, second] at hbound ⊢
          rw [← transverseInnerStencilError_terminal radius] at hbound
          exact hbound.trans (hfromError (4 * radius + 7))
        · by_cases hafterTerminal : index = 4 * radius + 8
          · subst index
            have hbound := norm_zeroPaddedSecondDifference_sliceProduct_after_terminal_le
              radius axis base component coordinate input
            dsimp [first, second] at hbound ⊢
            rw [← transverseInnerStencilError_afterTerminal radius] at hbound
            exact hbound.trans (hfromError (4 * radius + 8))
          · have hindex : index < 4 * radius + 7 := by omega
            by_cases hleftEntry : index = radius + 2
            · subst index
              rw [hproduct]
              have hbound :=
                norm_annularHodgeCoefficientSlice_secondDifference_leftEntry_le
                  radius axis base component coordinate input htransverse
              rw [← transverseInnerStencilError_leftEntry radius] at hbound
              exact hbound.trans (hfromError (radius + 2))
            · by_cases hleftExit : index = radius + 3
              · subst index
                rw [hproduct]
                have hbound :=
                  norm_annularHodgeCoefficientSlice_secondDifference_leftExit_le
                    radius axis base component coordinate input htransverse
                rw [← transverseInnerStencilError_leftExit radius] at hbound
                exact hbound.trans (hfromError (radius + 3))
              · by_cases hrightEntry : index = 3 * radius + 5
                · subst index
                  rw [hproduct]
                  have hbound :=
                    norm_annularHodgeCoefficientSlice_secondDifference_rightEntry_le
                      radius axis base component coordinate input htransverse
                  rw [← transverseInnerStencilError_rightEntry radius] at hbound
                  exact hbound.trans (hfromError (3 * radius + 5))
                · by_cases hrightExit : index = 3 * radius + 6
                  · subst index
                    rw [hproduct]
                    have hbound :=
                      norm_annularHodgeCoefficientSlice_secondDifference_rightExit_le
                        radius axis base component coordinate input htransverse
                    rw [← transverseInnerStencilError_rightExit radius] at hbound
                    exact hbound.trans (hfromError (3 * radius + 6))
                  · have htwo : 2 ≤ index := by omega
                    have hregion :
                        index ≤ radius + 1 ∨
                          (radius + 4 ≤ index ∧ index ≤ 3 * radius + 4) ∨
                          3 * radius + 7 ≤ index := by
                      omega
                    rcases hregion with hleft | hplateau | hright
                    · have hbound :=
                        norm_zeroPaddedSecondDifference_sliceProduct_le_of_active_outside
                          radius axis base component coordinate input hbaseOuter index htwo
                            hindex (Or.inl hleft)
                      dsimp [first, second] at hbound ⊢
                      exact hbound.trans (le_add_of_nonneg_right
                        (transverseInnerStencilError_nonneg radius index))
                    · rw [hproduct,
                        zeroPaddedSecondDifference_annularHodgeCoefficientSlice_eq_zero_of_inner_stencil
                          radius axis base component coordinate input htransverse index
                            hplateau.1 hplateau.2, norm_zero]
                      exact hfullNonneg index
                    · have hbound :=
                        norm_zeroPaddedSecondDifference_sliceProduct_le_of_active_outside
                          radius axis base component coordinate input hbaseOuter index htwo
                            hindex (Or.inr hright)
                      dsimp [first, second] at hbound ⊢
                      exact hbound.trans (le_add_of_nonneg_right
                        (transverseInnerStencilError_nonneg radius index))
  have hsum := sum_norm_zeroPaddedSecondDifference_mul_le_of_pointwiseError
    first second (4 * radius + 7) (8 / (radius + 2 : ℝ))
      (442 / (radius + 2 : ℝ) ^ 2) (transverseInnerStencilError radius) hpoint
  rw [hproduct] at hsum
  refine hsum.trans ?_
  rw [sum_transverseInnerStencilError]
  have hsecondVariation :=
    sum_norm_zeroPaddedSecondDifference_adjacentTensorSlice_le radius axis base
  have hfirstVariation :=
    sum_norm_zeroPaddedBackwardDifference_adjacentTensorSlice_le_eight radius axis base
  have hmass := sum_norm_adjacentTensorSlice_le radius axis base
  dsimp [first] at hsecondVariation hfirstVariation hmass ⊢
  gcongr

/-- Uniform reciprocal-scale form of the exhaustive transverse-inner estimate. -/
theorem sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1937_of_transverse_inner
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      1937 / (radius + 1 : ℝ) := by
  refine (sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse_inner
    radius axis base component coordinate input hbaseOuter htransverse).trans ?_
  have hfirst : 0 < (radius + 1 : ℝ) := by positivity
  have hsecond : 0 < (radius + 2 : ℝ) := by positivity
  field_simp [hfirst.ne', hsecond.ne']
  nlinarith [show (0 : ℝ) ≤ radius by positivity]

/-- Every outer-cube coordinate line satisfies the same reciprocal-scale second-variation bound:
the transverse coordinate is either active outside the inner cube or both transverse coordinates
lie in the inner plateau. -/
theorem sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1937
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hbaseOuter : base ∈ frequencyCube (valleePoussinOuterRadius (radius + 1))) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (annularHodgeCoefficientSlice radius axis base component coordinate input)
        (4 * radius + 7) index‖) ≤
      1937 / (radius + 1 : ℝ) := by
  classical
  by_cases htransverse : ∀ other : Fin 3, other ≠ axis →
      (base other).natAbs ≤ radius + 1
  · exact
      sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1937_of_transverse_inner
        radius axis base component coordinate input hbaseOuter htransverse
  · have houtside : ∃ other : Fin 3,
        other ≠ axis ∧ radius + 2 ≤ (base other).natAbs := by
      push_neg at htransverse
      rcases htransverse with ⟨other, hother, hlarge⟩
      exact ⟨other, hother, by omega⟩
    refine (sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1917
      radius axis base component coordinate input hbaseOuter houtside).trans ?_
    have hdenominator : 0 < (radius + 1 : ℝ) := by positivity
    exact (div_le_div_iff_of_pos_right hdenominator).2 (by norm_num)

section Audit

#print axioms norm_annularHodgeCoefficientSlice_secondDifference_leftEntry_le
#print axioms norm_annularHodgeCoefficientSlice_secondDifference_leftExit_le
#print axioms norm_annularHodgeCoefficientSlice_secondDifference_rightEntry_le
#print axioms norm_annularHodgeCoefficientSlice_secondDifference_rightExit_le
#print axioms sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_of_transverse_inner
#print axioms sum_norm_zeroPaddedSecondDifference_annularHodgeCoefficientSlice_le_1937

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum
