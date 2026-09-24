import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation

/-!
# Annular tensor coefficient variation

**[proved-derived]** This owner transports the exact scalar four-corner receiver through the
two-cell aperture shift separating adjacent de la Vallée Poussin scales, and then into the
coordinatewise tensor products used by the adjacent three-dimensional band.

The construction keeps zero padding and finite-difference populations explicit.  No physical
kernel bound is asserted until every coordinate-subset variation has the scale required by the
iterated Abel/Fubini receiver.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation

/-! ## Exact two-sided aperture shift -/

/-- Insert two exact zeros before and after a finite coefficient population. -/
def twoSidedPadTwo (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  if 2 ≤ index ∧ index < count + 2 then coefficient (index - 2) else 0

/-- Zero extension is unchanged when applied to an already two-sided padded population. -/
theorem zeroPaddedCoefficient_twoSidedPadTwo
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient (twoSidedPadTwo coefficient count) (count + 4) index =
      twoSidedPadTwo (zeroPaddedCoefficient coefficient count) count index := by
  simp only [zeroPaddedCoefficient, twoSidedPadTwo]
  split_ifs
  all_goals try omega
  all_goals rfl

/-- First backward differences commute exactly with the two-cell aperture shift. -/
theorem zeroPaddedBackwardDifference_twoSidedPadTwo
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedBackwardDifference (twoSidedPadTwo coefficient count)
        (count + 4) index =
      twoSidedPadTwo (zeroPaddedBackwardDifference coefficient count)
        (count + 1) index := by
  by_cases hsmall : index < 3
  · have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · subst index
      simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient, twoSidedPadTwo]
    · subst index
      simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient, twoSidedPadTwo]
    · subst index
      simp [zeroPaddedBackwardDifference, zeroPaddedCoefficient, twoSidedPadTwo]
  · have hzero : index ≠ 0 := by omega
    unfold zeroPaddedBackwardDifference
    rw [zeroPaddedCoefficient_twoSidedPadTwo, if_neg hzero,
      zeroPaddedCoefficient_twoSidedPadTwo]
    simp only [twoSidedPadTwo]
    split_ifs
    all_goals try omega
    all_goals try simp only [zeroPaddedCoefficient]
    all_goals try split_ifs
    all_goals try omega
    all_goals try (congr 2 <;> omega)
    all_goals ring

/-- Second differences commute exactly with the two-cell aperture shift. -/
theorem zeroPaddedSecondDifference_twoSidedPadTwo
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (twoSidedPadTwo coefficient count)
        (count + 4) index =
      twoSidedPadTwo (zeroPaddedSecondDifference coefficient count)
        (count + 2) index := by
  unfold zeroPaddedSecondDifference
  have hfirst :
      zeroPaddedBackwardDifference (twoSidedPadTwo coefficient count) (count + 4) =
        twoSidedPadTwo (zeroPaddedBackwardDifference coefficient count) (count + 1) := by
    funext position
    exact zeroPaddedBackwardDifference_twoSidedPadTwo coefficient count position
  rw [hfirst]
  simpa [zeroPaddedSecondDifference, Nat.add_assoc] using
    zeroPaddedBackwardDifference_twoSidedPadTwo
      (zeroPaddedBackwardDifference coefficient count) (count + 1) index

/-- A two-sided pad preserves total coefficient mass exactly. -/
theorem sum_norm_twoSidedPadTwo (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 4),
      ‖twoSidedPadTwo coefficient count index‖) =
      ∑ index ∈ Finset.range count, ‖coefficient index‖ := by
  have hmiddle :
      (∑ index ∈ Finset.range count,
        ‖if 2 ≤ 2 + index ∧ 2 + index < count + 2 then
            coefficient (2 + index - 2)
          else 0‖) =
        ∑ index ∈ Finset.range count, ‖coefficient index‖ := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    simp [show 2 ≤ 2 + index by omega,
      show 2 + index < count + 2 by omega,
      show 2 + index - 2 = index by omega]
  rw [show count + 4 = 2 + (count + 2) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    twoSidedPadTwo]
  rw [hmiddle]
  simp [show ¬2 + count < count + 2 by omega,
    show ¬2 + (count + 1) < count + 2 by omega]

/-- Total second variation is invariant under insertion of two exact zeros at each side. -/
theorem sum_norm_zeroPaddedSecondDifference_twoSidedPadTwo
    (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 6),
      ‖zeroPaddedSecondDifference (twoSidedPadTwo coefficient count)
        (count + 4) index‖) =
      ∑ index ∈ Finset.range (count + 2),
        ‖zeroPaddedSecondDifference coefficient count index‖ := by
  simp_rw [zeroPaddedSecondDifference_twoSidedPadTwo]
  exact sum_norm_twoSidedPadTwo
    (zeroPaddedSecondDifference coefficient count) (count + 2)

/-! ## Actual scalar charts in the adjacent aperture -/

/-- The base-radius scalar chart viewed in the next radius's centered aperture. -/
def baseCoordinateSliceInAdjacentAperture (radius index : ℕ) : ℂ :=
  (coordinateValleePoussinWeight radius
    (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index) : ℂ)

/-- The next-radius chart naturally uses the adjacent aperture. -/
def nextCoordinateSliceInAdjacentAperture (radius index : ℕ) : ℂ :=
  centeredCoordinateValleePoussinSlice (radius + 1) index

/-- The base chart in the adjacent aperture is exactly its natural profile with two zeros inserted
on each side. -/
theorem baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo
    (radius index : ℕ) :
    baseCoordinateSliceInAdjacentAperture radius index =
      twoSidedPadTwo (centeredValleePoussinProfile radius)
        (4 * radius + 3) index := by
  by_cases hinterior : 2 ≤ index ∧ index < 4 * radius + 5
  · have hfrequency :
        centeredFrequency (valleePoussinOuterRadius (radius + 1)) index =
          centeredFrequency (valleePoussinOuterRadius radius) (index - 2) := by
      unfold centeredFrequency valleePoussinOuterRadius
      omega
    simp only [baseCoordinateSliceInAdjacentAperture, twoSidedPadTwo, if_pos hinterior]
    rw [hfrequency]
    exact centeredCoordinateValleePoussinSlice_eq_profile radius (index - 2)
  · rw [twoSidedPadTwo, if_neg hinterior]
    by_cases hleft : index < 2
    · have hindexOuter : index ≤ valleePoussinOuterRadius (radius + 1) := by
        unfold valleePoussinOuterRadius
        omega
      have habs := natAbs_centeredFrequency_of_le hindexOuter
      have houtside :
          valleePoussinOuterRadius radius <
            (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index).natAbs := by
        rw [habs]
        unfold valleePoussinOuterRadius
        omega
      simp [baseCoordinateSliceInAdjacentAperture,
        coordinateValleePoussinWeight_eq_zero_of_outer_lt radius houtside]
    · have hright : 4 * radius + 5 ≤ index := by omega
      have hindexCenter : valleePoussinOuterRadius (radius + 1) ≤ index := by
        unfold valleePoussinOuterRadius
        omega
      have habs := natAbs_centeredFrequency_of_ge hindexCenter
      have houtside :
          valleePoussinOuterRadius radius <
            (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index).natAbs := by
        rw [habs]
        unfold valleePoussinOuterRadius
        omega
      simp [baseCoordinateSliceInAdjacentAperture,
        coordinateValleePoussinWeight_eq_zero_of_outer_lt radius houtside]

/-- Exact reciprocal second variation of the base chart after aperture transport. -/
theorem sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (baseCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖) =
      4 / (radius + 1 : ℝ) := by
  have hchart :
      baseCoordinateSliceInAdjacentAperture radius =
        twoSidedPadTwo (centeredValleePoussinProfile radius) (4 * radius + 3) := by
    funext index
    exact baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo radius index
  rw [hchart]
  have hshift := sum_norm_zeroPaddedSecondDifference_twoSidedPadTwo
    (centeredValleePoussinProfile radius) (4 * radius + 3)
  simpa only [show 4 * radius + 3 + 6 = 4 * radius + 9 by omega,
    show 4 * radius + 3 + 4 = 4 * radius + 7 by omega,
    show 4 * radius + 3 + 2 = 4 * radius + 5 by omega,
    sum_norm_zeroPaddedSecondDifference_centeredValleePoussinProfile] using hshift

/-- Exact reciprocal second variation of the next chart in its natural adjacent aperture. -/
theorem sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (nextCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖) =
      4 / (radius + 2 : ℝ) := by
  have hchart :
      nextCoordinateSliceInAdjacentAperture radius =
        centeredCoordinateValleePoussinSlice (radius + 1) := rfl
  rw [hchart]
  convert
    sum_norm_zeroPaddedSecondDifference_centeredCoordinateValleePoussinSlice (radius + 1)
      using 1 <;> norm_num <;> ring

/-! ## Adjacent one-coordinate chart -/

/-- Zero-padded first variation of the transported base chart remains uniformly bounded. -/
theorem sum_norm_zeroPaddedBackwardDifference_baseCoordinateSliceInAdjacentAperture_le_four
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖) ≤ 4 := by
  have hchart :
      baseCoordinateSliceInAdjacentAperture radius =
        twoSidedPadTwo (centeredValleePoussinProfile radius) (4 * radius + 3) := by
    funext index
    exact baseCoordinateSliceInAdjacentAperture_eq_twoSidedPadTwo radius index
  rw [hchart]
  simp_rw [zeroPaddedBackwardDifference_twoSidedPadTwo]
  have hmass := sum_norm_twoSidedPadTwo
    (zeroPaddedBackwardDifference (centeredValleePoussinProfile radius)
      (4 * radius + 3)) (4 * radius + 4)
  rw [show 4 * radius + 4 + 4 = 4 * radius + 8 by omega] at hmass
  rw [hmass]
  exact sum_norm_zeroPaddedBackwardDifference_centeredValleePoussinProfile_le_four radius

/-- Zero-padded first variation of the next chart is uniformly bounded in the adjacent aperture. -/
theorem sum_norm_zeroPaddedBackwardDifference_nextCoordinateSliceInAdjacentAperture_le_four
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖) ≤ 4 := by
  have hchart :
      nextCoordinateSliceInAdjacentAperture radius =
        centeredCoordinateValleePoussinSlice (radius + 1) := rfl
  rw [hchart]
  convert
    sum_norm_zeroPaddedBackwardDifference_centeredCoordinateValleePoussinSlice_le_four
      (radius + 1) using 1 <;> norm_num <;> ring

/-- Zero padding commutes with coefficient subtraction. -/
theorem zeroPaddedCoefficient_sub
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient (fun position ↦ first position - second position) count index =
      zeroPaddedCoefficient first count index - zeroPaddedCoefficient second count index := by
  simp only [zeroPaddedCoefficient]
  split_ifs <;> ring

/-- One zero-padded backward difference commutes with coefficient subtraction. -/
theorem zeroPaddedBackwardDifference_sub
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedBackwardDifference (fun position ↦ first position - second position) count index =
      zeroPaddedBackwardDifference first count index -
        zeroPaddedBackwardDifference second count index := by
  unfold zeroPaddedBackwardDifference
  rw [zeroPaddedCoefficient_sub]
  by_cases hzero : index = 0
  · simp [hzero]
  · rw [if_neg hzero, zeroPaddedCoefficient_sub]
    simp only [if_neg hzero]
    ring

/-- Two zero-padded backward differences commute with coefficient subtraction. -/
theorem zeroPaddedSecondDifference_sub
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (fun position ↦ first position - second position) count index =
      zeroPaddedSecondDifference first count index -
        zeroPaddedSecondDifference second count index := by
  unfold zeroPaddedSecondDifference
  have hfirst :
      zeroPaddedBackwardDifference (fun position ↦ first position - second position) count =
        fun position ↦ zeroPaddedBackwardDifference first count position -
          zeroPaddedBackwardDifference second count position := by
    funext position
    exact zeroPaddedBackwardDifference_sub first second count position
  rw [hfirst]
  exact zeroPaddedBackwardDifference_sub
    (zeroPaddedBackwardDifference first count)
    (zeroPaddedBackwardDifference second count) (count + 1) index

/-- The genuine adjacent one-coordinate chart in the common adjacent aperture. -/
def adjacentCoordinateSlice (radius index : ℕ) : ℂ :=
  nextCoordinateSliceInAdjacentAperture radius index -
    baseCoordinateSliceInAdjacentAperture radius index

/-- Each adjacent one-coordinate coefficient has magnitude at most one. -/
theorem norm_adjacentCoordinateSlice_le_one (radius index : ℕ) :
    ‖adjacentCoordinateSlice radius index‖ ≤ 1 := by
  let frequency := centeredFrequency (valleePoussinOuterRadius (radius + 1)) index
  have hnextNonneg := coordinateValleePoussinWeight_nonneg (radius + 1) frequency
  have hnextOne := coordinateValleePoussinWeight_le_one (radius + 1) frequency
  have hbaseNonneg := coordinateValleePoussinWeight_nonneg radius frequency
  have hbaseOne := coordinateValleePoussinWeight_le_one radius frequency
  change ‖((coordinateValleePoussinWeight (radius + 1) frequency : ℂ) -
    (coordinateValleePoussinWeight radius frequency : ℂ))‖ ≤ 1
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Linear coefficient mass of the adjacent one-coordinate chart. -/
theorem sum_norm_adjacentCoordinateSlice_le
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖adjacentCoordinateSlice radius index‖) ≤
      4 * radius + 7 := by
  calc
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖adjacentCoordinateSlice radius index‖) ≤
        ∑ _index ∈ Finset.range (4 * radius + 7), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_adjacentCoordinateSlice_le_one radius index
    _ = 4 * radius + 7 := by simp

/-- Uniform total first variation of the adjacent one-coordinate chart. -/
theorem sum_norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_eight
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (adjacentCoordinateSlice radius)
        (4 * radius + 7) index‖) ≤ 8 := by
  have hpoint : ∀ index,
      zeroPaddedBackwardDifference (adjacentCoordinateSlice radius)
          (4 * radius + 7) index =
        zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) index -
          zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) index := by
    intro index
    exact zeroPaddedBackwardDifference_sub _ _ _ _
  calc
    (∑ index ∈ Finset.range (4 * radius + 8),
      ‖zeroPaddedBackwardDifference (adjacentCoordinateSlice radius)
        (4 * radius + 7) index‖) ≤
      (∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖) +
      (∑ index ∈ Finset.range (4 * radius + 8),
        ‖zeroPaddedBackwardDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro index _hindex
      rw [hpoint index]
      exact norm_sub_le _ _
    _ ≤ 4 + 4 := add_le_add
      (sum_norm_zeroPaddedBackwardDifference_nextCoordinateSliceInAdjacentAperture_le_four radius)
      (sum_norm_zeroPaddedBackwardDifference_baseCoordinateSliceInAdjacentAperture_le_four radius)
    _ = 8 := by norm_num

/-- Reciprocal-scale total second variation of the adjacent one-coordinate chart. -/
theorem sum_norm_zeroPaddedSecondDifference_adjacentCoordinateSlice_le
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (adjacentCoordinateSlice radius)
        (4 * radius + 7) index‖) ≤
      8 / (radius + 1 : ℝ) := by
  have hpoint : ∀ index,
      zeroPaddedSecondDifference (adjacentCoordinateSlice radius)
          (4 * radius + 7) index =
        zeroPaddedSecondDifference (nextCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) index -
          zeroPaddedSecondDifference (baseCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) index := by
    intro index
    exact zeroPaddedSecondDifference_sub _ _ _ _
  calc
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (adjacentCoordinateSlice radius)
        (4 * radius + 7) index‖) ≤
      (∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖) +
      (∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro index _hindex
      rw [hpoint index]
      exact norm_sub_le _ _
    _ = 4 / (radius + 2 : ℝ) + 4 / (radius + 1 : ℝ) := by
      rw [sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture,
        sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture]
    _ ≤ 4 / (radius + 1 : ℝ) + 4 / (radius + 1 : ℝ) := by
      have hmono : (4 : ℝ) / (radius + 2 : ℝ) ≤
          4 / (radius + 1 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
      exact add_le_add hmono le_rfl
    _ = 8 / (radius + 1 : ℝ) := by ring

/-! ## Tensor-product coordinate slices -/

/-- Product of the two scalar coordinate weights transverse to an addressed axis. -/
def tensorCoordinateComplement
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) : ℝ :=
  ∏ coordinate ∈ Finset.univ.erase axis,
    coordinateValleePoussinWeight radius (base coordinate)

/-- Exact factorization of a tensor multiplier along one addressed coordinate. -/
theorem tensorValleePoussinWeight_replaceFrequencyCoordinate
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (value : ℤ) :
    tensorValleePoussinWeight radius
        (replaceFrequencyCoordinate axis base value) =
      coordinateValleePoussinWeight radius value *
        tensorCoordinateComplement radius axis base := by
  unfold tensorValleePoussinWeight tensorCoordinateComplement
  symm
  calc
    coordinateValleePoussinWeight radius value *
        ∏ coordinate ∈ Finset.univ.erase axis,
          coordinateValleePoussinWeight radius (base coordinate) =
      coordinateValleePoussinWeight radius
          (replaceFrequencyCoordinate axis base value axis) *
        ∏ coordinate ∈ Finset.univ.erase axis,
          coordinateValleePoussinWeight radius
            (replaceFrequencyCoordinate axis base value coordinate) := by
      congr 1
      · simp [replaceFrequencyCoordinate]
      · apply Finset.prod_congr rfl
        intro coordinate hcoordinate
        have hne : coordinate ≠ axis := Finset.ne_of_mem_erase hcoordinate
        simp [replaceFrequencyCoordinate, hne]
    _ = ∏ coordinate : Fin 3,
          coordinateValleePoussinWeight radius
            (replaceFrequencyCoordinate axis base value coordinate) :=
      Finset.mul_prod_erase Finset.univ
        (fun coordinate : Fin 3 ↦ coordinateValleePoussinWeight radius
          (replaceFrequencyCoordinate axis base value coordinate))
        (Finset.mem_univ axis)

/-- Every transverse tensor complement lies in the unit interval. -/
theorem tensorCoordinateComplement_mem_unitInterval
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    0 ≤ tensorCoordinateComplement radius axis base ∧
      tensorCoordinateComplement radius axis base ≤ 1 := by
  constructor
  · unfold tensorCoordinateComplement
    exact Finset.prod_nonneg fun coordinate _ ↦
      coordinateValleePoussinWeight_nonneg radius (base coordinate)
  · unfold tensorCoordinateComplement
    apply Finset.prod_le_one
    · intro coordinate _
      exact coordinateValleePoussinWeight_nonneg radius (base coordinate)
    · intro coordinate _
      exact coordinateValleePoussinWeight_le_one radius (base coordinate)

/-- The next tensor low-pass restricted to one coordinate in the common adjacent aperture. -/
def nextTensorSliceInAdjacentAperture
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) : ℂ :=
  (tensorValleePoussinWeight (radius + 1)
    (replaceFrequencyCoordinate axis base
      (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index)) : ℂ)

/-- The base tensor low-pass restricted to the same common adjacent aperture. -/
def baseTensorSliceInAdjacentAperture
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) : ℂ :=
  (tensorValleePoussinWeight radius
    (replaceFrequencyCoordinate axis base
      (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index)) : ℂ)

/-- Next tensor slices factor into the next scalar chart and a constant transverse complement. -/
theorem nextTensorSliceInAdjacentAperture_eq
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) :
    nextTensorSliceInAdjacentAperture radius axis base index =
      nextCoordinateSliceInAdjacentAperture radius index *
        (tensorCoordinateComplement (radius + 1) axis base : ℂ) := by
  simp only [nextTensorSliceInAdjacentAperture, nextCoordinateSliceInAdjacentAperture,
    centeredCoordinateValleePoussinSlice]
  rw [tensorValleePoussinWeight_replaceFrequencyCoordinate]
  push_cast
  rfl

/-- Base tensor slices factor into the shifted base scalar chart and its transverse complement. -/
theorem baseTensorSliceInAdjacentAperture_eq
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) :
    baseTensorSliceInAdjacentAperture radius axis base index =
      baseCoordinateSliceInAdjacentAperture radius index *
        (tensorCoordinateComplement radius axis base : ℂ) := by
  simp only [baseTensorSliceInAdjacentAperture, baseCoordinateSliceInAdjacentAperture]
  rw [tensorValleePoussinWeight_replaceFrequencyCoordinate]
  push_cast
  rfl

/-- Zero padding commutes with multiplication by a constant coefficient. -/
theorem zeroPaddedCoefficient_mul_right
    (coefficient : ℕ → ℂ) (constant : ℂ) (count index : ℕ) :
    zeroPaddedCoefficient (fun position ↦ coefficient position * constant) count index =
      zeroPaddedCoefficient coefficient count index * constant := by
  simp only [zeroPaddedCoefficient]
  split_ifs <;> ring

/-- One zero-padded backward difference commutes with multiplication by a constant. -/
theorem zeroPaddedBackwardDifference_mul_right
    (coefficient : ℕ → ℂ) (constant : ℂ) (count index : ℕ) :
    zeroPaddedBackwardDifference (fun position ↦ coefficient position * constant) count index =
      zeroPaddedBackwardDifference coefficient count index * constant := by
  unfold zeroPaddedBackwardDifference
  rw [zeroPaddedCoefficient_mul_right]
  by_cases hzero : index = 0
  · simp [hzero]
  · rw [if_neg hzero, zeroPaddedCoefficient_mul_right]
    simp only [if_neg hzero]
    ring

/-- Two zero-padded backward differences commute with multiplication by a constant. -/
theorem zeroPaddedSecondDifference_mul_right
    (coefficient : ℕ → ℂ) (constant : ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (fun position ↦ coefficient position * constant) count index =
      zeroPaddedSecondDifference coefficient count index * constant := by
  unfold zeroPaddedSecondDifference
  have hfirst :
      zeroPaddedBackwardDifference (fun position ↦ coefficient position * constant) count =
        fun position ↦ zeroPaddedBackwardDifference coefficient count position * constant := by
    funext position
    exact zeroPaddedBackwardDifference_mul_right coefficient constant count position
  rw [hfirst]
  exact zeroPaddedBackwardDifference_mul_right
    (zeroPaddedBackwardDifference coefficient count) constant (count + 1) index

/-- Complex norm of every transverse tensor complement is at most one. -/
theorem norm_tensorCoordinateComplement_le_one
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    ‖(tensorCoordinateComplement radius axis base : ℂ)‖ ≤ 1 := by
  obtain ⟨hnonneg, hone⟩ := tensorCoordinateComplement_mem_unitInterval radius axis base
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hone

/-- Reciprocal second variation of a next tensor low-pass along any addressed coordinate. -/
theorem sum_norm_zeroPaddedSecondDifference_nextTensorSliceInAdjacentAperture_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (nextTensorSliceInAdjacentAperture radius axis base)
        (4 * radius + 7) index‖) ≤
      4 / (radius + 2 : ℝ) := by
  have hslice :
      nextTensorSliceInAdjacentAperture radius axis base =
        fun index ↦ nextCoordinateSliceInAdjacentAperture radius index *
          (tensorCoordinateComplement (radius + 1) axis base : ℂ) := by
    funext index
    exact nextTensorSliceInAdjacentAperture_eq radius axis base index
  rw [hslice]
  simp_rw [zeroPaddedSecondDifference_mul_right, norm_mul]
  calc
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (nextCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ *
          ‖(tensorCoordinateComplement (radius + 1) axis base : ℂ)‖) ≤
      ∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ * 1 := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact mul_le_mul_of_nonneg_left
        (norm_tensorCoordinateComplement_le_one (radius + 1) axis base) (norm_nonneg _)
    _ = 4 / (radius + 2 : ℝ) := by
      simp only [mul_one]
      exact sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture radius

/-- Reciprocal second variation of a transported base tensor low-pass along any coordinate. -/
theorem sum_norm_zeroPaddedSecondDifference_baseTensorSliceInAdjacentAperture_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference
        (baseTensorSliceInAdjacentAperture radius axis base)
        (4 * radius + 7) index‖) ≤
      4 / (radius + 1 : ℝ) := by
  have hslice :
      baseTensorSliceInAdjacentAperture radius axis base =
        fun index ↦ baseCoordinateSliceInAdjacentAperture radius index *
          (tensorCoordinateComplement radius axis base : ℂ) := by
    funext index
    exact baseTensorSliceInAdjacentAperture_eq radius axis base index
  rw [hslice]
  simp_rw [zeroPaddedSecondDifference_mul_right, norm_mul]
  calc
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (baseCoordinateSliceInAdjacentAperture radius)
        (4 * radius + 7) index‖ *
          ‖(tensorCoordinateComplement radius axis base : ℂ)‖) ≤
      ∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) index‖ * 1 := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact mul_le_mul_of_nonneg_left
        (norm_tensorCoordinateComplement_le_one radius axis base) (norm_nonneg _)
    _ = 4 / (radius + 1 : ℝ) := by
      simp only [mul_one]
      exact sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture radius

/-- The actual adjacent tensor multiplier restricted to one addressed coordinate. -/
def adjacentTensorSlice
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) : ℂ :=
  nextTensorSliceInAdjacentAperture radius axis base index -
    baseTensorSliceInAdjacentAperture radius axis base index

/-- The tensor slice is definitionally the genuine adjacent multiplier on the reindexed lattice. -/
theorem adjacentTensorSlice_eq_actual
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) :
    adjacentTensorSlice radius axis base index =
      (adjacentValleePoussinWeight radius
        (replaceFrequencyCoordinate axis base
          (centeredFrequency (valleePoussinOuterRadius (radius + 1)) index)) : ℂ) := by
  simp [adjacentTensorSlice, nextTensorSliceInAdjacentAperture,
    baseTensorSliceInAdjacentAperture, adjacentValleePoussinWeight]

/-- Each actual adjacent tensor coefficient has magnitude at most one. -/
theorem norm_adjacentTensorSlice_le_one
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) (index : ℕ) :
    ‖adjacentTensorSlice radius axis base index‖ ≤ 1 := by
  rw [adjacentTensorSlice_eq_actual, Complex.norm_real, Real.norm_eq_abs]
  exact abs_adjacentValleePoussinWeight_le_one radius _

/-- Sharp linear population scaling for every coordinate slice of the actual adjacent tensor. -/
theorem sum_norm_adjacentTensorSlice_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖adjacentTensorSlice radius axis base index‖) ≤
      4 * radius + 7 := by
  calc
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖adjacentTensorSlice radius axis base index‖) ≤
      ∑ _index ∈ Finset.range (4 * radius + 7), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_adjacentTensorSlice_le_one radius axis base index
    _ = 4 * radius + 7 := by simp

/-- Reciprocal-scale total second variation of the actual adjacent tensor in every coordinate
slice, uniformly in the two transverse coordinates. -/
theorem sum_norm_zeroPaddedSecondDifference_adjacentTensorSlice_le
    (radius : ℕ) (axis : Fin 3) (base : SpatialFrequency) :
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index‖) ≤
      8 / (radius + 1 : ℝ) := by
  have hpoint : ∀ index,
      zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
          (4 * radius + 7) index =
        zeroPaddedSecondDifference (nextTensorSliceInAdjacentAperture radius axis base)
            (4 * radius + 7) index -
          zeroPaddedSecondDifference (baseTensorSliceInAdjacentAperture radius axis base)
            (4 * radius + 7) index := by
    intro index
    exact zeroPaddedSecondDifference_sub _ _ _ _
  calc
    (∑ index ∈ Finset.range (4 * radius + 9),
      ‖zeroPaddedSecondDifference (adjacentTensorSlice radius axis base)
        (4 * radius + 7) index‖) ≤
      (∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (nextTensorSliceInAdjacentAperture radius axis base)
          (4 * radius + 7) index‖) +
      (∑ index ∈ Finset.range (4 * radius + 9),
        ‖zeroPaddedSecondDifference (baseTensorSliceInAdjacentAperture radius axis base)
          (4 * radius + 7) index‖) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro index _hindex
      rw [hpoint index]
      exact norm_sub_le _ _
    _ ≤ 4 / (radius + 2 : ℝ) + 4 / (radius + 1 : ℝ) :=
      add_le_add
        (sum_norm_zeroPaddedSecondDifference_nextTensorSliceInAdjacentAperture_le
          radius axis base)
        (sum_norm_zeroPaddedSecondDifference_baseTensorSliceInAdjacentAperture_le
          radius axis base)
    _ ≤ 4 / (radius + 1 : ℝ) + 4 / (radius + 1 : ℝ) := by
      have hmono : (4 : ℝ) / (radius + 2 : ℝ) ≤
          4 / (radius + 1 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
      exact add_le_add hmono le_rfl
    _ = 8 / (radius + 1 : ℝ) := by ring

/-! ## Coordinate-subset difference identities -/

/-- Second differences also commute with multiplication on the left by a constant. -/
theorem zeroPaddedSecondDifference_mul_left
    (constant : ℂ) (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (fun position ↦ constant * coefficient position) count index =
      constant * zeroPaddedSecondDifference coefficient count index := by
  have hfunctions :
      (fun position ↦ constant * coefficient position) =
        fun position ↦ coefficient position * constant := by
    funext position
    ring
  rw [hfunctions, zeroPaddedSecondDifference_mul_right]
  ring

/-- A separated three-coordinate scalar tensor. -/
def separatedTensorCoefficient
    (first second third : ℕ → ℂ) (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  first firstIndex * second secondIndex * third thirdIndex

/-- Second difference in the first coordinate of a separated tensor. -/
def separatedTensorSecondDifferenceFirst
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun position ↦ separatedTensorCoefficient first second third
      position secondIndex thirdIndex)
    count firstIndex

/-- Mixed second differences in the first two coordinates of a separated tensor. -/
def separatedTensorSecondDifferenceFirstSecond
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedMixedSecondDifference
    (fun firstPosition secondPosition ↦ separatedTensorCoefficient first second third
      firstPosition secondPosition thirdIndex)
    count count firstIndex secondIndex

/-- Mixed second differences in all three coordinates of a separated tensor. -/
def separatedTensorSecondDifferenceAll
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun firstPosition ↦ zeroPaddedMixedSecondDifference
      (fun secondPosition thirdPosition ↦ separatedTensorCoefficient first second third
        firstPosition secondPosition thirdPosition)
      count count secondIndex thirdIndex)
    count firstIndex

/-- A first-coordinate second difference acts only on the first separated factor. -/
theorem separatedTensorSecondDifferenceFirst_eq
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    separatedTensorSecondDifferenceFirst first second third count
        firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifference first count firstIndex *
        second secondIndex * third thirdIndex := by
  unfold separatedTensorSecondDifferenceFirst separatedTensorCoefficient
  have h := zeroPaddedSecondDifference_mul_right first
    (second secondIndex * third thirdIndex) count firstIndex
  simpa [mul_assoc] using h

/-- Mixed first/second coordinate differences factor as the product of the two scalar second
differences and the untouched third coefficient. -/
theorem separatedTensorSecondDifferenceFirstSecond_eq
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    separatedTensorSecondDifferenceFirstSecond first second third count
        firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifference first count firstIndex *
        zeroPaddedSecondDifference second count secondIndex *
          third thirdIndex := by
  unfold separatedTensorSecondDifferenceFirstSecond zeroPaddedMixedSecondDifference
    separatedTensorCoefficient
  have hinner :
      (fun firstPosition ↦ zeroPaddedSecondDifference
        (fun secondPosition ↦ first firstPosition * second secondPosition * third thirdIndex)
        count secondIndex) =
      fun firstPosition ↦ first firstPosition *
        (zeroPaddedSecondDifference second count secondIndex * third thirdIndex) := by
    funext firstPosition
    have hleft := zeroPaddedSecondDifference_mul_left
      (first firstPosition) second count secondIndex
    have hright := zeroPaddedSecondDifference_mul_right
      (fun secondPosition ↦ first firstPosition * second secondPosition)
      (third thirdIndex) count secondIndex
    rw [hright, hleft]
    ring
  rw [hinner, zeroPaddedSecondDifference_mul_right]
  ring

/-- Three coordinatewise second-difference passages factor completely on a separated tensor. -/
theorem separatedTensorSecondDifferenceAll_eq
    (first second third : ℕ → ℂ) (count : ℕ)
    (firstIndex secondIndex thirdIndex : ℕ) :
    separatedTensorSecondDifferenceAll first second third count
        firstIndex secondIndex thirdIndex =
      zeroPaddedSecondDifference first count firstIndex *
        zeroPaddedSecondDifference second count secondIndex *
          zeroPaddedSecondDifference third count thirdIndex := by
  unfold separatedTensorSecondDifferenceAll
  have hinner :
      (fun firstPosition ↦ zeroPaddedMixedSecondDifference
        (fun secondPosition thirdPosition ↦ separatedTensorCoefficient first second third
          firstPosition secondPosition thirdPosition)
        count count secondIndex thirdIndex) =
      fun firstPosition ↦ first firstPosition *
        (zeroPaddedSecondDifference second count secondIndex *
          zeroPaddedSecondDifference third count thirdIndex) := by
    funext firstPosition
    unfold zeroPaddedMixedSecondDifference separatedTensorCoefficient
    have hthird :
        (fun secondPosition ↦ zeroPaddedSecondDifference
          (fun thirdPosition ↦ first firstPosition * second secondPosition * third thirdPosition)
          count thirdIndex) =
        fun secondPosition ↦ first firstPosition * second secondPosition *
          zeroPaddedSecondDifference third count thirdIndex := by
      funext secondPosition
      have h := zeroPaddedSecondDifference_mul_left
        (first firstPosition * second secondPosition) third count thirdIndex
      simpa [mul_assoc] using h
    rw [hthird]
    have h := zeroPaddedSecondDifference_mul_right second
      (zeroPaddedSecondDifference third count thirdIndex) count secondIndex
    simpa [zeroPaddedSecondDifference_mul_left, mul_assoc] using
      congrArg (fun value ↦ first firstPosition * value) h
  rw [hinner, zeroPaddedSecondDifference_mul_right]
  ring

/-! ## Exact tensor-product mass identities -/

/-- The norm mass of a separated three-coordinate population factors exactly into the three
one-coordinate norm masses. -/
theorem sum_norm_separatedTensorCoefficient
    (first second third : ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖separatedTensorCoefficient first second third
            firstIndex secondIndex thirdIndex‖) =
      (∑ firstIndex ∈ Finset.range firstCount, ‖first firstIndex‖) *
        (∑ secondIndex ∈ Finset.range secondCount, ‖second secondIndex‖) *
          (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
  simp_rw [separatedTensorCoefficient, norm_mul]
  calc
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖first firstIndex‖ * ‖second secondIndex‖ * ‖third thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range firstCount,
        (‖first firstIndex‖ *
          (∑ secondIndex ∈ Finset.range secondCount, ‖second secondIndex‖)) *
            (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
      apply Finset.sum_congr rfl
      intro firstIndex _hfirstIndex
      calc
        (∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            ‖first firstIndex‖ * ‖second secondIndex‖ * ‖third thirdIndex‖) =
          ∑ secondIndex ∈ Finset.range secondCount,
            (‖first firstIndex‖ * ‖second secondIndex‖) *
              (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
            apply Finset.sum_congr rfl
            intro secondIndex _hsecondIndex
            rw [Finset.mul_sum]
        _ =
          (∑ secondIndex ∈ Finset.range secondCount,
            ‖first firstIndex‖ * ‖second secondIndex‖) *
              (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
            exact (Finset.sum_mul (Finset.range secondCount)
              (fun secondIndex ↦ ‖first firstIndex‖ * ‖second secondIndex‖)
              (∑ thirdIndex ∈ Finset.range thirdCount,
                ‖third thirdIndex‖)).symm
        _ =
          (‖first firstIndex‖ *
            (∑ secondIndex ∈ Finset.range secondCount, ‖second secondIndex‖)) *
              (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
            congr 1
            exact (Finset.mul_sum (Finset.range secondCount)
              (fun secondIndex ↦ ‖second secondIndex‖)
              ‖first firstIndex‖).symm
    _ =
      (∑ firstIndex ∈ Finset.range firstCount, ‖first firstIndex‖) *
        (∑ secondIndex ∈ Finset.range secondCount, ‖second secondIndex‖) *
          (∑ thirdIndex ∈ Finset.range thirdCount, ‖third thirdIndex‖) := by
      rw [Finset.sum_mul, Finset.sum_mul]

/-- Exact Fubini factorization after a second-difference passage in the first coordinate. -/
theorem sum_norm_separatedTensorSecondDifferenceFirst
    (first second third : ℕ → ℂ) (count differenceCount : ℕ) :
    (∑ firstIndex ∈ Finset.range differenceCount,
      ∑ secondIndex ∈ Finset.range count,
        ∑ thirdIndex ∈ Finset.range count,
          ‖separatedTensorSecondDifferenceFirst first second third count
            firstIndex secondIndex thirdIndex‖) =
      (∑ firstIndex ∈ Finset.range differenceCount,
        ‖zeroPaddedSecondDifference first count firstIndex‖) *
        (∑ secondIndex ∈ Finset.range count, ‖second secondIndex‖) *
          (∑ thirdIndex ∈ Finset.range count, ‖third thirdIndex‖) := by
  simp_rw [separatedTensorSecondDifferenceFirst_eq]
  exact sum_norm_separatedTensorCoefficient
    (zeroPaddedSecondDifference first count) second third
    differenceCount count count

/-- Exact Fubini factorization after second differences in two coordinate directions. -/
theorem sum_norm_separatedTensorSecondDifferenceFirstSecond
    (first second third : ℕ → ℂ) (count differenceCount : ℕ) :
    (∑ firstIndex ∈ Finset.range differenceCount,
      ∑ secondIndex ∈ Finset.range differenceCount,
        ∑ thirdIndex ∈ Finset.range count,
          ‖separatedTensorSecondDifferenceFirstSecond first second third count
            firstIndex secondIndex thirdIndex‖) =
      (∑ firstIndex ∈ Finset.range differenceCount,
        ‖zeroPaddedSecondDifference first count firstIndex‖) *
        (∑ secondIndex ∈ Finset.range differenceCount,
          ‖zeroPaddedSecondDifference second count secondIndex‖) *
          (∑ thirdIndex ∈ Finset.range count, ‖third thirdIndex‖) := by
  simp_rw [separatedTensorSecondDifferenceFirstSecond_eq]
  exact sum_norm_separatedTensorCoefficient
    (zeroPaddedSecondDifference first count)
    (zeroPaddedSecondDifference second count) third
    differenceCount differenceCount count

/-- Exact Fubini factorization after second differences in all three coordinate directions. -/
theorem sum_norm_separatedTensorSecondDifferenceAll
    (first second third : ℕ → ℂ) (count differenceCount : ℕ) :
    (∑ firstIndex ∈ Finset.range differenceCount,
      ∑ secondIndex ∈ Finset.range differenceCount,
        ∑ thirdIndex ∈ Finset.range differenceCount,
          ‖separatedTensorSecondDifferenceAll first second third count
            firstIndex secondIndex thirdIndex‖) =
      (∑ firstIndex ∈ Finset.range differenceCount,
        ‖zeroPaddedSecondDifference first count firstIndex‖) *
        (∑ secondIndex ∈ Finset.range differenceCount,
          ‖zeroPaddedSecondDifference second count secondIndex‖) *
          (∑ thirdIndex ∈ Finset.range differenceCount,
            ‖zeroPaddedSecondDifference third count thirdIndex‖) := by
  simp_rw [separatedTensorSecondDifferenceAll_eq]
  exact sum_norm_separatedTensorCoefficient
    (zeroPaddedSecondDifference first count)
    (zeroPaddedSecondDifference second count)
    (zeroPaddedSecondDifference third count)
    differenceCount differenceCount differenceCount

/-! ## The actual adjacent three-coordinate cube -/

/-- Every next-radius scalar chart coefficient has norm at most one. -/
theorem norm_nextCoordinateSliceInAdjacentAperture_le_one
    (radius index : ℕ) :
    ‖nextCoordinateSliceInAdjacentAperture radius index‖ ≤ 1 := by
  let frequency := centeredFrequency (valleePoussinOuterRadius (radius + 1)) index
  have hnonneg := coordinateValleePoussinWeight_nonneg (radius + 1) frequency
  have hone := coordinateValleePoussinWeight_le_one (radius + 1) frequency
  change ‖(coordinateValleePoussinWeight (radius + 1) frequency : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hone

/-- Every transported base-radius scalar chart coefficient has norm at most one. -/
theorem norm_baseCoordinateSliceInAdjacentAperture_le_one
    (radius index : ℕ) :
    ‖baseCoordinateSliceInAdjacentAperture radius index‖ ≤ 1 := by
  let frequency := centeredFrequency (valleePoussinOuterRadius (radius + 1)) index
  have hnonneg := coordinateValleePoussinWeight_nonneg radius frequency
  have hone := coordinateValleePoussinWeight_le_one radius frequency
  change ‖(coordinateValleePoussinWeight radius frequency : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hone

/-- Sharp aperture-count mass bound for the next scalar chart. -/
theorem sum_norm_nextCoordinateSliceInAdjacentAperture_le_count
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖nextCoordinateSliceInAdjacentAperture radius index‖) ≤
      (4 * radius + 7 : ℝ) := by
  calc
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖nextCoordinateSliceInAdjacentAperture radius index‖) ≤
        ∑ _index ∈ Finset.range (4 * radius + 7), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_nextCoordinateSliceInAdjacentAperture_le_one radius index
    _ = (4 * radius + 7 : ℝ) := by simp

/-- Sharp aperture-count mass bound for the transported base scalar chart. -/
theorem sum_norm_baseCoordinateSliceInAdjacentAperture_le_count
    (radius : ℕ) :
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖baseCoordinateSliceInAdjacentAperture radius index‖) ≤
      (4 * radius + 7 : ℝ) := by
  calc
    (∑ index ∈ Finset.range (4 * radius + 7),
      ‖baseCoordinateSliceInAdjacentAperture radius index‖) ≤
        ∑ _index ∈ Finset.range (4 * radius + 7), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro index _hindex
      exact norm_baseCoordinateSliceInAdjacentAperture_le_one radius index
    _ = (4 * radius + 7 : ℝ) := by simp

/-- The common centered three-dimensional aperture for adjacent radii. -/
def adjacentApertureFrequency
    (radius firstIndex secondIndex thirdIndex : ℕ) : SpatialFrequency :=
  ![centeredFrequency (valleePoussinOuterRadius (radius + 1)) firstIndex,
    centeredFrequency (valleePoussinOuterRadius (radius + 1)) secondIndex,
    centeredFrequency (valleePoussinOuterRadius (radius + 1)) thirdIndex]

/-- The next low-pass scalar tensor on the common adjacent cube. -/
def nextTensorCubeCoefficient
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (nextCoordinateSliceInAdjacentAperture radius)
    (nextCoordinateSliceInAdjacentAperture radius)
    (nextCoordinateSliceInAdjacentAperture radius)
    firstIndex secondIndex thirdIndex

/-- The transported base low-pass scalar tensor on the common adjacent cube. -/
def baseTensorCubeCoefficient
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  separatedTensorCoefficient
    (baseCoordinateSliceInAdjacentAperture radius)
    (baseCoordinateSliceInAdjacentAperture radius)
    (baseCoordinateSliceInAdjacentAperture radius)
    firstIndex secondIndex thirdIndex

/-- The genuine adjacent tensor multiplier on its complete centered coefficient cube. -/
def adjacentTensorCubeCoefficient
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  nextTensorCubeCoefficient radius firstIndex secondIndex thirdIndex -
    baseTensorCubeCoefficient radius firstIndex secondIndex thirdIndex

/-- The separated next-radius cube is exactly the genuine next tensor multiplier. -/
theorem nextTensorCubeCoefficient_eq_actual
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    nextTensorCubeCoefficient radius firstIndex secondIndex thirdIndex =
      (tensorValleePoussinWeight (radius + 1)
        (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex) : ℂ) := by
  simp [nextTensorCubeCoefficient, separatedTensorCoefficient,
    nextCoordinateSliceInAdjacentAperture, centeredCoordinateValleePoussinSlice,
    tensorValleePoussinWeight, adjacentApertureFrequency, Fin.prod_univ_three]

/-- The separated transported base cube is exactly the genuine base tensor multiplier. -/
theorem baseTensorCubeCoefficient_eq_actual
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    baseTensorCubeCoefficient radius firstIndex secondIndex thirdIndex =
      (tensorValleePoussinWeight radius
        (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex) : ℂ) := by
  simp [baseTensorCubeCoefficient, separatedTensorCoefficient,
    baseCoordinateSliceInAdjacentAperture, tensorValleePoussinWeight,
    adjacentApertureFrequency, Fin.prod_univ_three]

/-- The cube difference is exactly `adjacentValleePoussinWeight`, not a surrogate chart. -/
theorem adjacentTensorCubeCoefficient_eq_actual
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    adjacentTensorCubeCoefficient radius firstIndex secondIndex thirdIndex =
      (adjacentValleePoussinWeight radius
        (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex) : ℂ) := by
  rw [adjacentTensorCubeCoefficient, nextTensorCubeCoefficient_eq_actual,
    baseTensorCubeCoefficient_eq_actual]
  simp [adjacentValleePoussinWeight]

/-- Every coefficient of the genuine adjacent three-dimensional cube has norm at most one. -/
theorem norm_adjacentTensorCubeCoefficient_le_one
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    ‖adjacentTensorCubeCoefficient radius firstIndex secondIndex thirdIndex‖ ≤ 1 := by
  rw [adjacentTensorCubeCoefficient_eq_actual, Complex.norm_real, Real.norm_eq_abs]
  exact abs_adjacentValleePoussinWeight_le_one radius _

/-- Sharp cubic population scaling for the undifferentiated adjacent tensor cube. -/
theorem sum_norm_adjacentTensorCubeCoefficient_le_cube
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 7),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeCoefficient radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 * radius + 7 : ℝ) ^ 3 := by
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 7),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeCoefficient radius
            firstIndex secondIndex thirdIndex‖) ≤
      ∑ _firstIndex ∈ Finset.range (4 * radius + 7),
        ∑ _secondIndex ∈ Finset.range (4 * radius + 7),
          ∑ _thirdIndex ∈ Finset.range (4 * radius + 7), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro firstIndex _hfirstIndex
      apply Finset.sum_le_sum
      intro secondIndex _hsecondIndex
      apply Finset.sum_le_sum
      intro thirdIndex _hthirdIndex
      exact norm_adjacentTensorCubeCoefficient_le_one radius
        firstIndex secondIndex thirdIndex
    _ = (4 * radius + 7 : ℝ) ^ 3 := by
      simp
      ring

/-- Second difference of the actual adjacent cube in its first displayed coordinate. -/
def adjacentTensorCubeSecondDifferenceFirst
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun position ↦ adjacentTensorCubeCoefficient radius position secondIndex thirdIndex)
    (4 * radius + 7) firstIndex

/-- Mixed second difference of the actual adjacent cube in its first two displayed coordinates. -/
def adjacentTensorCubeSecondDifferenceFirstSecond
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedMixedSecondDifference
    (fun firstPosition secondPosition ↦
      adjacentTensorCubeCoefficient radius firstPosition secondPosition thirdIndex)
    (4 * radius + 7) (4 * radius + 7) firstIndex secondIndex

/-- Three coordinatewise second differences of the actual adjacent cube. -/
def adjacentTensorCubeSecondDifferenceAll
    (radius firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun firstPosition ↦ zeroPaddedMixedSecondDifference
      (fun secondPosition thirdPosition ↦
        adjacentTensorCubeCoefficient radius firstPosition secondPosition thirdPosition)
      (4 * radius + 7) (4 * radius + 7) secondIndex thirdIndex)
    (4 * radius + 7) firstIndex

/-- Mixed zero-padded second differences commute with coefficient subtraction. -/
theorem zeroPaddedMixedSecondDifference_sub
    (first second : ℕ → ℕ → ℂ)
    (firstCount secondCount firstIndex secondIndex : ℕ) :
    zeroPaddedMixedSecondDifference
        (fun firstPosition secondPosition ↦
          first firstPosition secondPosition - second firstPosition secondPosition)
        firstCount secondCount firstIndex secondIndex =
      zeroPaddedMixedSecondDifference first
          firstCount secondCount firstIndex secondIndex -
        zeroPaddedMixedSecondDifference second
          firstCount secondCount firstIndex secondIndex := by
  unfold zeroPaddedMixedSecondDifference
  have hinner :
      (fun firstPosition ↦ zeroPaddedSecondDifference
        (fun secondPosition ↦
          first firstPosition secondPosition - second firstPosition secondPosition)
        secondCount secondIndex) =
      fun firstPosition ↦
        zeroPaddedSecondDifference (first firstPosition) secondCount secondIndex -
          zeroPaddedSecondDifference (second firstPosition) secondCount secondIndex := by
    funext firstPosition
    exact zeroPaddedSecondDifference_sub
      (first firstPosition) (second firstPosition) secondCount secondIndex
  rw [hinner]
  exact zeroPaddedSecondDifference_sub _ _ firstCount firstIndex

/-- The one-coordinate receiver of the actual adjacent cube is the difference of the two
separated low-pass receivers. -/
theorem adjacentTensorCubeSecondDifferenceFirst_eq_sub
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    adjacentTensorCubeSecondDifferenceFirst radius
        firstIndex secondIndex thirdIndex =
      separatedTensorSecondDifferenceFirst
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex -
        separatedTensorSecondDifferenceFirst
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex := by
  unfold adjacentTensorCubeSecondDifferenceFirst adjacentTensorCubeCoefficient
    nextTensorCubeCoefficient baseTensorCubeCoefficient
    separatedTensorSecondDifferenceFirst
  exact zeroPaddedSecondDifference_sub _ _ _ _

/-- The two-coordinate receiver of the actual adjacent cube is the difference of the two
separated low-pass receivers. -/
theorem adjacentTensorCubeSecondDifferenceFirstSecond_eq_sub
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    adjacentTensorCubeSecondDifferenceFirstSecond radius
        firstIndex secondIndex thirdIndex =
      separatedTensorSecondDifferenceFirstSecond
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex -
        separatedTensorSecondDifferenceFirstSecond
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex := by
  unfold adjacentTensorCubeSecondDifferenceFirstSecond adjacentTensorCubeCoefficient
    nextTensorCubeCoefficient baseTensorCubeCoefficient
    separatedTensorSecondDifferenceFirstSecond
  exact zeroPaddedMixedSecondDifference_sub _ _ _ _ _ _

/-- The three-coordinate receiver of the actual adjacent cube is the difference of the two
separated low-pass receivers. -/
theorem adjacentTensorCubeSecondDifferenceAll_eq_sub
    (radius firstIndex secondIndex thirdIndex : ℕ) :
    adjacentTensorCubeSecondDifferenceAll radius
        firstIndex secondIndex thirdIndex =
      separatedTensorSecondDifferenceAll
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (nextCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex -
        separatedTensorSecondDifferenceAll
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (baseCoordinateSliceInAdjacentAperture radius)
          (4 * radius + 7) firstIndex secondIndex thirdIndex := by
  unfold adjacentTensorCubeSecondDifferenceAll adjacentTensorCubeCoefficient
    nextTensorCubeCoefficient baseTensorCubeCoefficient
    separatedTensorSecondDifferenceAll
  have hinner :
      (fun firstPosition ↦ zeroPaddedMixedSecondDifference
        (fun secondPosition thirdPosition ↦
          separatedTensorCoefficient
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              firstPosition secondPosition thirdPosition -
            separatedTensorCoefficient
              (baseCoordinateSliceInAdjacentAperture radius)
              (baseCoordinateSliceInAdjacentAperture radius)
              (baseCoordinateSliceInAdjacentAperture radius)
              firstPosition secondPosition thirdPosition)
        (4 * radius + 7) (4 * radius + 7) secondIndex thirdIndex) =
      fun firstPosition ↦
        zeroPaddedMixedSecondDifference
            (fun secondPosition thirdPosition ↦ separatedTensorCoefficient
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              firstPosition secondPosition thirdPosition)
            (4 * radius + 7) (4 * radius + 7) secondIndex thirdIndex -
          zeroPaddedMixedSecondDifference
            (fun secondPosition thirdPosition ↦ separatedTensorCoefficient
              (baseCoordinateSliceInAdjacentAperture radius)
              (baseCoordinateSliceInAdjacentAperture radius)
              (baseCoordinateSliceInAdjacentAperture radius)
              firstPosition secondPosition thirdPosition)
            (4 * radius + 7) (4 * radius + 7) secondIndex thirdIndex := by
    funext firstPosition
    exact zeroPaddedMixedSecondDifference_sub _ _ _ _ _ _
  rw [hinner]
  exact zeroPaddedSecondDifference_sub _ _ _ _

/-- Triangle inequality after three finite Fubini sums. -/
theorem sum_sum_sum_norm_sub_le
    (first second : ℕ → ℕ → ℕ → ℂ)
    (firstCount secondCount thirdCount : ℕ) :
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖first firstIndex secondIndex thirdIndex -
            second firstIndex secondIndex thirdIndex‖) ≤
      (∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            ‖first firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖second firstIndex secondIndex thirdIndex‖ := by
  calc
    (∑ firstIndex ∈ Finset.range firstCount,
      ∑ secondIndex ∈ Finset.range secondCount,
        ∑ thirdIndex ∈ Finset.range thirdCount,
          ‖first firstIndex secondIndex thirdIndex -
            second firstIndex secondIndex thirdIndex‖) ≤
      ∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            (‖first firstIndex secondIndex thirdIndex‖ +
              ‖second firstIndex secondIndex thirdIndex‖) := by
      apply Finset.sum_le_sum
      intro firstIndex _hfirstIndex
      apply Finset.sum_le_sum
      intro secondIndex _hsecondIndex
      apply Finset.sum_le_sum
      intro thirdIndex _hthirdIndex
      exact norm_sub_le _ _
    _ =
      (∑ firstIndex ∈ Finset.range firstCount,
        ∑ secondIndex ∈ Finset.range secondCount,
          ∑ thirdIndex ∈ Finset.range thirdCount,
            ‖first firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range firstCount,
          ∑ secondIndex ∈ Finset.range secondCount,
            ∑ thirdIndex ∈ Finset.range thirdCount,
              ‖second firstIndex secondIndex thirdIndex‖ := by
      simp only [Finset.sum_add_distrib]

/-! ## Sharp scale laws for separated low-pass cubes -/

/-- One-coordinate second variation of the next tensor cube has exact `N² / radius` scaling. -/
theorem sum_norm_nextTensorCubeSecondDifferenceFirst_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖separatedTensorSecondDifferenceFirst
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) * (4 * radius + 7 : ℝ) *
        (4 * radius + 7 : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirst,
    sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture]
  gcongr
  · exact sum_norm_nextCoordinateSliceInAdjacentAperture_le_count radius
  · exact sum_norm_nextCoordinateSliceInAdjacentAperture_le_count radius

/-- One-coordinate second variation of the transported base cube has exact `N² / radius`
scaling. -/
theorem sum_norm_baseTensorCubeSecondDifferenceFirst_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖separatedTensorSecondDifferenceFirst
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
        (4 * radius + 7 : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirst,
    sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture]
  gcongr
  · exact sum_norm_baseCoordinateSliceInAdjacentAperture_le_count radius
  · exact sum_norm_baseCoordinateSliceInAdjacentAperture_le_count radius

/-- Two-coordinate second variation of the next tensor cube has exact `N / radius²` scaling. -/
theorem sum_norm_nextTensorCubeSecondDifferenceFirstSecond_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖separatedTensorSecondDifferenceFirstSecond
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirstSecond,
    sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture]
  calc
    (4 / (radius + 2 : ℝ)) * (4 / (radius + 2 : ℝ)) *
        (∑ index ∈ Finset.range (4 * radius + 7),
          ‖nextCoordinateSliceInAdjacentAperture radius index‖) ≤
      (4 / (radius + 2 : ℝ)) * (4 / (radius + 2 : ℝ)) *
        (4 * radius + 7 : ℝ) := by
      gcongr
      exact sum_norm_nextCoordinateSliceInAdjacentAperture_le_count radius
    _ = (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) := by ring

/-- Two-coordinate second variation of the transported base cube has exact `N / radius²`
scaling. -/
theorem sum_norm_baseTensorCubeSecondDifferenceFirstSecond_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖separatedTensorSecondDifferenceFirstSecond
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) := by
  rw [sum_norm_separatedTensorSecondDifferenceFirstSecond,
    sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture]
  calc
    (4 / (radius + 1 : ℝ)) * (4 / (radius + 1 : ℝ)) *
        (∑ index ∈ Finset.range (4 * radius + 7),
          ‖baseCoordinateSliceInAdjacentAperture radius index‖) ≤
      (4 / (radius + 1 : ℝ)) * (4 / (radius + 1 : ℝ)) *
        (4 * radius + 7 : ℝ) := by
      gcongr
      exact sum_norm_baseCoordinateSliceInAdjacentAperture_le_count radius
    _ = (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) := by ring

/-- Three-coordinate second variation of the next tensor cube is exactly cubic in the reciprocal
scale. -/
theorem sum_norm_nextTensorCubeSecondDifferenceAll
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖separatedTensorSecondDifferenceAll
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (nextCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) =
      (4 / (radius + 2 : ℝ)) ^ 3 := by
  rw [sum_norm_separatedTensorSecondDifferenceAll,
    sum_norm_zeroPaddedSecondDifference_nextCoordinateSliceInAdjacentAperture]
  ring

/-- Three-coordinate second variation of the transported base tensor cube is exactly cubic in the
reciprocal scale. -/
theorem sum_norm_baseTensorCubeSecondDifferenceAll
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖separatedTensorSecondDifferenceAll
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (baseCoordinateSliceInAdjacentAperture radius)
            (4 * radius + 7) firstIndex secondIndex thirdIndex‖) =
      (4 / (radius + 1 : ℝ)) ^ 3 := by
  rw [sum_norm_separatedTensorSecondDifferenceAll,
    sum_norm_zeroPaddedSecondDifference_baseCoordinateSliceInAdjacentAperture]
  ring

/-! ## Sharp coordinate-subset variation of the actual adjacent tensor -/

/-- The genuine adjacent cube has the sum of the two exact one-coordinate scale bounds. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceFirst_le_precise
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirst radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) := by
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirst radius
            firstIndex secondIndex thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 7),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
            ‖separatedTensorSecondDifferenceFirst
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex -
              separatedTensorSecondDifferenceFirst
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ := by
        simp_rw [adjacentTensorCubeSecondDifferenceFirst_eq_sub]
    _ ≤
      (∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 7),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
            ‖separatedTensorSecondDifferenceFirst
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (4 * radius + 7) firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range (4 * radius + 9),
          ∑ secondIndex ∈ Finset.range (4 * radius + 7),
            ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
              ‖separatedTensorSecondDifferenceFirst
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ :=
      sum_sum_sum_norm_sub_le _ _ _ _ _
    _ ≤
      (4 / (radius + 2 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) :=
      add_le_add
        (sum_norm_nextTensorCubeSecondDifferenceFirst_le radius)
        (sum_norm_baseTensorCubeSecondDifferenceFirst_le radius)

/-- The genuine adjacent cube has the sum of the two exact mixed-coordinate scale bounds. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceFirstSecond_le_precise
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirstSecond radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) := by
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirstSecond radius
            firstIndex secondIndex thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 9),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
            ‖separatedTensorSecondDifferenceFirstSecond
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex -
              separatedTensorSecondDifferenceFirstSecond
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ := by
        simp_rw [adjacentTensorCubeSecondDifferenceFirstSecond_eq_sub]
    _ ≤
      (∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 9),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
            ‖separatedTensorSecondDifferenceFirstSecond
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (4 * radius + 7) firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range (4 * radius + 9),
          ∑ secondIndex ∈ Finset.range (4 * radius + 9),
            ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
              ‖separatedTensorSecondDifferenceFirstSecond
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ :=
      sum_sum_sum_norm_sub_le _ _ _ _ _
    _ ≤
      (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) :=
      add_le_add
        (sum_norm_nextTensorCubeSecondDifferenceFirstSecond_le radius)
        (sum_norm_baseTensorCubeSecondDifferenceFirstSecond_le radius)

/-- The fully differenced genuine adjacent cube has the sum of the two exact reciprocal-cubic
scale masses. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceAll_le_precise
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖adjacentTensorCubeSecondDifferenceAll radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) ^ 3 +
        (4 / (radius + 1 : ℝ)) ^ 3 := by
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖adjacentTensorCubeSecondDifferenceAll radius
            firstIndex secondIndex thirdIndex‖) =
      ∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 9),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
            ‖separatedTensorSecondDifferenceAll
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (nextCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex -
              separatedTensorSecondDifferenceAll
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ := by
        simp_rw [adjacentTensorCubeSecondDifferenceAll_eq_sub]
    _ ≤
      (∑ firstIndex ∈ Finset.range (4 * radius + 9),
        ∑ secondIndex ∈ Finset.range (4 * radius + 9),
          ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
            ‖separatedTensorSecondDifferenceAll
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (nextCoordinateSliceInAdjacentAperture radius)
              (4 * radius + 7) firstIndex secondIndex thirdIndex‖) +
        ∑ firstIndex ∈ Finset.range (4 * radius + 9),
          ∑ secondIndex ∈ Finset.range (4 * radius + 9),
            ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
              ‖separatedTensorSecondDifferenceAll
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (baseCoordinateSliceInAdjacentAperture radius)
                (4 * radius + 7) firstIndex secondIndex thirdIndex‖ :=
      sum_sum_sum_norm_sub_le _ _ _ _ _
    _ =
      (4 / (radius + 2 : ℝ)) ^ 3 +
        (4 / (radius + 1 : ℝ)) ^ 3 := by
      rw [sum_norm_nextTensorCubeSecondDifferenceAll,
        sum_norm_baseTensorCubeSecondDifferenceAll]

/-- Radius-normalized one-coordinate subset law for the genuine adjacent cube. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceFirst_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirst radius
            firstIndex secondIndex thirdIndex‖) ≤
      (8 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
        (4 * radius + 7 : ℝ) := by
  have hscale : (4 : ℝ) / (radius + 2 : ℝ) ≤
      4 / (radius + 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
  have hterm :
      (4 / (radius + 2 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) ≤
        (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) := by
    gcongr
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 7),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirst radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) :=
      sum_norm_adjacentTensorCubeSecondDifferenceFirst_le_precise radius
    _ ≤
      (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
          (4 * radius + 7 : ℝ) := add_le_add hterm le_rfl
    _ =
      (8 / (radius + 1 : ℝ)) * (4 * radius + 7 : ℝ) *
        (4 * radius + 7 : ℝ) := by ring

/-- Radius-normalized two-coordinate subset law for the genuine adjacent cube. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceFirstSecond_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirstSecond radius
            firstIndex secondIndex thirdIndex‖) ≤
      (32 / (radius + 1 : ℝ) ^ 2) * (4 * radius + 7 : ℝ) := by
  have hscale : (4 : ℝ) / (radius + 2 : ℝ) ≤
      4 / (radius + 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
  have hsquare : (4 / (radius + 2 : ℝ)) ^ 2 ≤
      (4 / (radius + 1 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hscale 2
  have hterm :
      (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) ≤
        (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) :=
    mul_le_mul_of_nonneg_right hsquare (by positivity)
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 7),
          ‖adjacentTensorCubeSecondDifferenceFirstSecond radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) :=
      sum_norm_adjacentTensorCubeSecondDifferenceFirstSecond_le_precise radius
    _ ≤
      (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) +
        (4 / (radius + 1 : ℝ)) ^ 2 * (4 * radius + 7 : ℝ) :=
      add_le_add hterm le_rfl
    _ = (32 / (radius + 1 : ℝ) ^ 2) * (4 * radius + 7 : ℝ) := by
      have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-- Radius-normalized three-coordinate subset law for the genuine adjacent cube. -/
theorem sum_norm_adjacentTensorCubeSecondDifferenceAll_le
    (radius : ℕ) :
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖adjacentTensorCubeSecondDifferenceAll radius
            firstIndex secondIndex thirdIndex‖) ≤
      128 / (radius + 1 : ℝ) ^ 3 := by
  have hscale : (4 : ℝ) / (radius + 2 : ℝ) ≤
      4 / (radius + 1 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by norm_num)
  have hcubic : (4 / (radius + 2 : ℝ)) ^ 3 ≤
      (4 / (radius + 1 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hscale 3
  calc
    (∑ firstIndex ∈ Finset.range (4 * radius + 9),
      ∑ secondIndex ∈ Finset.range (4 * radius + 9),
        ∑ thirdIndex ∈ Finset.range (4 * radius + 9),
          ‖adjacentTensorCubeSecondDifferenceAll radius
            firstIndex secondIndex thirdIndex‖) ≤
      (4 / (radius + 2 : ℝ)) ^ 3 +
        (4 / (radius + 1 : ℝ)) ^ 3 :=
      sum_norm_adjacentTensorCubeSecondDifferenceAll_le_precise radius
    _ ≤ (4 / (radius + 1 : ℝ)) ^ 3 +
        (4 / (radius + 1 : ℝ)) ^ 3 := add_le_add hcubic le_rfl
    _ = 128 / (radius + 1 : ℝ) ^ 3 := by
      have hdenominator : (radius + 1 : ℝ) ≠ 0 := by positivity
      field_simp
      ring

section Audit

#print axioms sum_norm_zeroPaddedBackwardDifference_adjacentCoordinateSlice_le_eight
#print axioms sum_norm_zeroPaddedSecondDifference_adjacentTensorSlice_le
#print axioms adjacentTensorCubeCoefficient_eq_actual
#print axioms sum_norm_adjacentTensorCubeCoefficient_le_cube
#print axioms sum_norm_adjacentTensorCubeSecondDifferenceFirst_le
#print axioms sum_norm_adjacentTensorCubeSecondDifferenceFirstSecond_le
#print axioms sum_norm_adjacentTensorCubeSecondDifferenceAll_le

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
