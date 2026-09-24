import ElementaryHolonics.Millennium.NavierStokesAnnularTensorCoefficientVariation

/-!
# Localized variation of the annular Hodge multiplier

**[proved-derived]** This owner joins the exact coordinate-subset scale laws for the genuine
adjacent de la Vallée Poussin tensor to the rational Hodge multiplier entry.  It keeps the inner
plateau cancellation explicit, including stencils which cross the totalized zero mode, and records
the exact zero-padded product rule needed to transfer localized rational first and second
differences into the physical Abel/Fubini receiver.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation

/-! ## The actual Hodge coefficient cube and its inner cancellation -/

/-- One addressed entry of the actual adjacent Hodge multiplier on the complete centered cube. -/
def annularHodgeCubeCoefficient
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  adjacentTensorCubeCoefficient radius firstIndex secondIndex thirdIndex *
    hodgeJacobianMultiplierEntry
      (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex)
      component coordinate input

/-- The cube chart is exactly the already-defined genuine annular Hodge multiplier coefficient. -/
theorem annularHodgeCubeCoefficient_eq_actual
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) :
    annularHodgeCubeCoefficient radius component coordinate input
        firstIndex secondIndex thirdIndex =
      annularHodgeMultiplierCoefficient radius
        (adjacentApertureFrequency radius firstIndex secondIndex thirdIndex)
        component coordinate input := by
  rw [annularHodgeCubeCoefficient, adjacentTensorCubeCoefficient_eq_actual]
  rfl

/-- Centered cube indices in the displayed interval represent frequencies in the inner plateau. -/
theorem adjacentApertureFrequency_mem_inner_of_index_bounds
    (radius firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : radius + 2 ≤ firstIndex ∧ firstIndex ≤ 3 * radius + 4)
    (hsecond : radius + 2 ≤ secondIndex ∧ secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    adjacentApertureFrequency radius firstIndex secondIndex thirdIndex ∈
      frequencyCube (radius + 1) := by
  rw [mem_frequencyCube_iff]
  intro axis
  fin_cases axis <;>
    simp [adjacentApertureFrequency, centeredFrequency, valleePoussinOuterRadius] <;>
    omega

/-- Every actual Hodge entry vanishes exactly on the inner plateau cube. -/
theorem annularHodgeCubeCoefficient_eq_zero_of_index_bounds
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirst : radius + 2 ≤ firstIndex ∧ firstIndex ≤ 3 * radius + 4)
    (hsecond : radius + 2 ≤ secondIndex ∧ secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    annularHodgeCubeCoefficient radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  rw [annularHodgeCubeCoefficient_eq_actual]
  exact adjacentHodgeJacobianMultiplierEntry_eq_zero_of_mem_inner radius
    (adjacentApertureFrequency_mem_inner_of_index_bounds radius
      firstIndex secondIndex thirdIndex hfirst hsecond hthird)
    component coordinate input

/-! ## Exact zero-padded product transport -/

/-- Zero extension commutes with pointwise multiplication. -/
theorem zeroPaddedCoefficient_mul
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient (fun position ↦ first position * second position) count index =
      zeroPaddedCoefficient first count index *
        zeroPaddedCoefficient second count index := by
  simp only [zeroPaddedCoefficient]
  split_ifs <;> ring

/-- The zero-padded coefficient one position behind the addressed index. -/
def zeroPaddedPreviousCoefficient
    (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  if index = 0 then 0 else
    zeroPaddedCoefficient coefficient count (index - 1)

/-- The zero-padded coefficient two positions behind the addressed index. -/
def zeroPaddedSecondPreviousCoefficient
    (coefficient : ℕ → ℂ) (count index : ℕ) : ℂ :=
  if index < 2 then 0 else
    zeroPaddedCoefficient coefficient count (index - 2)

/-- Re-extending a first-difference population by its exact support length changes nothing. -/
theorem zeroPaddedCoefficient_zeroPaddedBackwardDifference
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedCoefficient (zeroPaddedBackwardDifference coefficient count)
        (count + 1) index =
      zeroPaddedBackwardDifference coefficient count index := by
  by_cases hinterior : index < count + 1
  · simp [zeroPaddedCoefficient, hinterior]
  · have hcount : count ≤ index := by omega
    have hprevious : count ≤ index - 1 := by omega
    simp [zeroPaddedCoefficient, zeroPaddedBackwardDifference, hinterior,
      show ¬index < count by omega, show index ≠ 0 by omega,
      show ¬index - 1 < count by omega]

/-- A first backward difference is current coefficient minus the exact zero-padded predecessor. -/
theorem zeroPaddedBackwardDifference_eq_current_sub_previous
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedBackwardDifference coefficient count index =
      zeroPaddedCoefficient coefficient count index -
        zeroPaddedPreviousCoefficient coefficient count index := by
  rfl

/-- The second difference is the exact three-corner combination, including both aperture
boundaries. -/
theorem zeroPaddedSecondDifference_eq_three_coefficients
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference coefficient count index =
      zeroPaddedCoefficient coefficient count index -
        2 * zeroPaddedPreviousCoefficient coefficient count index +
          zeroPaddedSecondPreviousCoefficient coefficient count index := by
  unfold zeroPaddedSecondDifference
  rw [zeroPaddedBackwardDifference_eq_current_sub_previous,
    zeroPaddedCoefficient_zeroPaddedBackwardDifference]
  by_cases hzero : index = 0
  · subst index
    simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
      zeroPaddedBackwardDifference_eq_current_sub_previous]
  · unfold zeroPaddedPreviousCoefficient at *
    rw [if_neg hzero,
      zeroPaddedCoefficient_zeroPaddedBackwardDifference,
      zeroPaddedBackwardDifference_eq_current_sub_previous,
      zeroPaddedBackwardDifference_eq_current_sub_previous]
    by_cases hone : index = 1
    · subst index
      simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient]
      ring
    · have htwo : 2 ≤ index := by omega
      simp only [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
        if_neg hzero, if_neg (show ¬index < 2 by omega),
        if_neg (show index - 1 ≠ 0 by omega)]
      rw [show index - 1 - 1 = index - 2 by omega]
      ring

/-- One-position zero padding commutes with pointwise multiplication. -/
theorem zeroPaddedPreviousCoefficient_mul
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedPreviousCoefficient (fun position ↦ first position * second position)
        count index =
      zeroPaddedPreviousCoefficient first count index *
        zeroPaddedPreviousCoefficient second count index := by
  simp only [zeroPaddedPreviousCoefficient]
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_mul first second count (index - 1)

/-- Two-position zero padding commutes with pointwise multiplication. -/
theorem zeroPaddedSecondPreviousCoefficient_mul
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondPreviousCoefficient
        (fun position ↦ first position * second position) count index =
      zeroPaddedSecondPreviousCoefficient first count index *
        zeroPaddedSecondPreviousCoefficient second count index := by
  simp only [zeroPaddedSecondPreviousCoefficient]
  split_ifs
  · ring
  · exact zeroPaddedCoefficient_mul first second count (index - 2)

/-- Exact zero-padded second-difference Leibniz rule.  The three terms are scalar curvature,
first-difference interaction, and rational curvature; the two boundary shifts are explicitly
zeroed, so the identity remains valid at both ends of the finite aperture. -/
theorem zeroPaddedSecondDifference_mul
    (first second : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedSecondDifference (fun position ↦ first position * second position)
        count index =
      zeroPaddedSecondDifference first count index *
          zeroPaddedCoefficient second count index +
        2 * (zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index) *
            (zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index) +
        zeroPaddedSecondPreviousCoefficient first count index *
            zeroPaddedSecondDifference second count index := by
  rw [zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedSecondDifference_eq_three_coefficients,
    zeroPaddedCoefficient_mul, zeroPaddedPreviousCoefficient_mul,
    zeroPaddedSecondPreviousCoefficient_mul]
  ring

/-- Norm receiver for the exact zero-padded Leibniz rule. -/
theorem norm_zeroPaddedSecondDifference_mul_le
    (first second : ℕ → ℂ) (count index : ℕ) :
    ‖zeroPaddedSecondDifference (fun position ↦ first position * second position)
        count index‖ ≤
      ‖zeroPaddedSecondDifference first count index‖ *
          ‖zeroPaddedCoefficient second count index‖ +
        2 * ‖zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index‖ *
            ‖zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index‖ +
        ‖zeroPaddedSecondPreviousCoefficient first count index‖ *
            ‖zeroPaddedSecondDifference second count index‖ := by
  rw [zeroPaddedSecondDifference_mul]
  calc
      ‖zeroPaddedSecondDifference first count index *
          zeroPaddedCoefficient second count index +
        2 * (zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index) *
            (zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index) +
        zeroPaddedSecondPreviousCoefficient first count index *
            zeroPaddedSecondDifference second count index‖ ≤
      ‖zeroPaddedSecondDifference first count index *
          zeroPaddedCoefficient second count index +
        2 * (zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index) *
            (zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index)‖ +
        ‖zeroPaddedSecondPreviousCoefficient first count index *
            zeroPaddedSecondDifference second count index‖ := norm_add_le _ _
    _ ≤
      (‖zeroPaddedSecondDifference first count index *
          zeroPaddedCoefficient second count index‖ +
        ‖2 * (zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index) *
            (zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index)‖) +
        ‖zeroPaddedSecondPreviousCoefficient first count index *
            zeroPaddedSecondDifference second count index‖ := by
      gcongr
      exact norm_add_le _ _
    _ =
      ‖zeroPaddedSecondDifference first count index‖ *
          ‖zeroPaddedCoefficient second count index‖ +
        2 * ‖zeroPaddedPreviousCoefficient first count index -
          zeroPaddedSecondPreviousCoefficient first count index‖ *
            ‖zeroPaddedCoefficient second count index -
              zeroPaddedPreviousCoefficient second count index‖ +
        ‖zeroPaddedSecondPreviousCoefficient first count index‖ *
            ‖zeroPaddedSecondDifference second count index‖ := by
      simp only [norm_mul]
      rw [show ‖(2 : ℂ)‖ = 2 by norm_num]

/-! ## Stencils crossing the totalized zero mode -/

/-- The actual first-coordinate second-difference receiver for one Hodge entry. -/
def annularHodgeCubeSecondDifferenceFirst
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ) : ℂ :=
  zeroPaddedSecondDifference
    (fun position ↦ annularHodgeCubeCoefficient radius component coordinate input
      position secondIndex thirdIndex)
    (4 * radius + 7) firstIndex

/-- Any three-point first-coordinate stencil wholly inside the plateau vanishes.  This is the
localized alternative to attempting a rational-symbol derivative through the zero mode. -/
theorem annularHodgeCubeSecondDifferenceFirst_eq_zero_of_stencil_mem_inner
    (radius : ℕ) (component coordinate input : Fin 3)
    (firstIndex secondIndex thirdIndex : ℕ)
    (hfirstLower : radius + 4 ≤ firstIndex)
    (hfirstUpper : firstIndex ≤ 3 * radius + 4)
    (hsecond : radius + 2 ≤ secondIndex ∧ secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    annularHodgeCubeSecondDifferenceFirst radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 := by
  have hcurrent : annularHodgeCubeCoefficient radius component coordinate input
      firstIndex secondIndex thirdIndex = 0 :=
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds radius component coordinate input
      firstIndex secondIndex thirdIndex
      ⟨by omega, hfirstUpper⟩ hsecond hthird
  have hprevious : annularHodgeCubeCoefficient radius component coordinate input
      (firstIndex - 1) secondIndex thirdIndex = 0 :=
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds radius component coordinate input
      (firstIndex - 1) secondIndex thirdIndex
      ⟨by omega, by omega⟩ hsecond hthird
  have hsecondPrevious : annularHodgeCubeCoefficient radius component coordinate input
      (firstIndex - 2) secondIndex thirdIndex = 0 :=
    annularHodgeCubeCoefficient_eq_zero_of_index_bounds radius component coordinate input
      (firstIndex - 2) secondIndex thirdIndex
      ⟨by omega, by omega⟩ hsecond hthird
  unfold annularHodgeCubeSecondDifferenceFirst
  rw [zeroPaddedSecondDifference_eq_three_coefficients]
  simp [zeroPaddedCoefficient, zeroPaddedPreviousCoefficient,
    zeroPaddedSecondPreviousCoefficient,
    show firstIndex < 4 * radius + 7 by omega,
    show firstIndex ≠ 0 by omega,
    show firstIndex - 1 < 4 * radius + 7 by omega,
    show ¬firstIndex < 2 by omega,
    show firstIndex - 2 < 4 * radius + 7 by omega,
    hcurrent, hprevious, hsecondPrevious]

/-- The centered indices `outer+1`, `outer`, and `outer-1` are exactly the frequencies `1`, `0`,
and `-1`. -/
theorem centeredFrequency_zero_crossing_values (radius : ℕ) :
    centeredFrequency (valleePoussinOuterRadius (radius + 1)) (2 * radius + 4) = 1 ∧
      centeredFrequency (valleePoussinOuterRadius (radius + 1)) (2 * radius + 3) = 0 ∧
        centeredFrequency (valleePoussinOuterRadius (radius + 1)) (2 * radius + 2) = -1 := by
  unfold centeredFrequency valleePoussinOuterRadius
  constructor <;> omega

/-- In particular, the stencil which literally crosses the totalized zero frequency contributes
zero whenever its transverse coordinates remain in the inner plateau. -/
theorem annularHodgeCubeSecondDifferenceFirst_eq_zero_at_zero_crossing
    (radius : ℕ) (component coordinate input : Fin 3)
    (secondIndex thirdIndex : ℕ)
    (hsecond : radius + 2 ≤ secondIndex ∧ secondIndex ≤ 3 * radius + 4)
    (hthird : radius + 2 ≤ thirdIndex ∧ thirdIndex ≤ 3 * radius + 4) :
    annularHodgeCubeSecondDifferenceFirst radius component coordinate input
      (2 * radius + 4) secondIndex thirdIndex = 0 := by
  exact annularHodgeCubeSecondDifferenceFirst_eq_zero_of_stencil_mem_inner
    radius component coordinate input (2 * radius + 4) secondIndex thirdIndex
    (by omega) (by omega) hsecond hthird

/-! ## Denominator scale away from the inner plateau -/

/-- Outside the inner plateau cube, one integer coordinate has magnitude at least `radius + 2`. -/
theorem exists_coordinate_natAbs_ge_of_not_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube (radius + 1)) :
    ∃ axis : Fin 3, radius + 2 ≤ (frequency axis).natAbs := by
  by_contra hnot
  push_neg at hnot
  apply hfrequency
  rw [mem_frequencyCube_iff]
  intro axis
  apply (natAbs_le_iff_bounds (radius + 1) (frequency axis)).mp
  have haxis := hnot axis
  omega

/-- The Hodge denominator has the correct quadratic scale outside the cancelled inner cube. -/
theorem radius_add_two_sq_le_frequencySquared_of_not_mem_inner
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube (radius + 1)) :
    (radius + 2 : ℝ) ^ 2 ≤ frequencySquared frequency := by
  obtain ⟨axis, haxis⟩ :=
    exists_coordinate_natAbs_ge_of_not_mem_inner radius hfrequency
  have habs : (radius + 2 : ℝ) ≤ |(frequency axis : ℝ)| := by
    have hcast : (radius + 2 : ℝ) ≤ ((frequency axis).natAbs : ℝ) := by
      exact_mod_cast haxis
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
  have hsquare : (radius + 2 : ℝ) ^ 2 ≤ (frequency axis : ℝ) ^ 2 := by
    have hsquareAbs := pow_le_pow_left₀ (by positivity) habs 2
    simpa only [sq_abs] using hsquareAbs
  have hterm : (frequency axis : ℝ) ^ 2 ≤ frequencySquared frequency := by
    unfold frequencySquared
    exact Finset.single_le_sum
      (fun other _hother ↦ sq_nonneg (frequency other : ℝ)) (Finset.mem_univ axis)
  exact hsquare.trans hterm

/-! ## One-step rational Hodge variation on a localized annulus -/

/-- Increment one addressed integer frequency coordinate by one lattice unit. -/
def incrementFrequencyCoordinate
    (axis : Fin 3) (frequency : SpatialFrequency) : SpatialFrequency :=
  replaceFrequencyCoordinate axis frequency (frequency axis + 1)

@[simp]
theorem incrementFrequencyCoordinate_apply_same
    (axis : Fin 3) (frequency : SpatialFrequency) :
    incrementFrequencyCoordinate axis frequency axis = frequency axis + 1 := by
  simp [incrementFrequencyCoordinate, replaceFrequencyCoordinate]

@[simp]
theorem incrementFrequencyCoordinate_apply_of_ne
    {axis other : Fin 3} (haxes : other ≠ axis) (frequency : SpatialFrequency) :
    incrementFrequencyCoordinate axis frequency other = frequency other := by
  simp [incrementFrequencyCoordinate, replaceFrequencyCoordinate, haxes]

/-- Exact change of the quadratic Hodge denominator under one coordinate increment. -/
theorem frequencySquared_incrementFrequencyCoordinate
    (axis : Fin 3) (frequency : SpatialFrequency) :
    frequencySquared (incrementFrequencyCoordinate axis frequency) =
      frequencySquared frequency + 2 * (frequency axis : ℝ) + 1 := by
  fin_cases axis <;>
    simp [incrementFrequencyCoordinate, replaceFrequencyCoordinate,
      frequencySquared, Fin.sum_univ_succ] <;>
    push_cast <;>
    ring

/-- Each complex coordinate changes by norm at most one under a unit increment. -/
theorem norm_incrementFrequencyCoordinate_sub_le_one
    (axis other : Fin 3) (frequency : SpatialFrequency) :
    ‖(incrementFrequencyCoordinate axis frequency other : ℂ) -
        (frequency other : ℂ)‖ ≤ 1 := by
  by_cases haxes : other = axis
  · subst other
    simp [incrementFrequencyCoordinate_apply_same]
  · rw [incrementFrequencyCoordinate_apply_of_ne haxes]
    simp

/-- A coordinatewise radius bound grows by at most one after a unit increment. -/
theorem norm_incrementFrequencyCoordinate_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (axis other : Fin 3) :
    ‖(incrementFrequencyCoordinate axis frequency other : ℂ)‖ ≤ bound + 1 := by
  calc
    ‖(incrementFrequencyCoordinate axis frequency other : ℂ)‖ =
      ‖((incrementFrequencyCoordinate axis frequency other : ℂ) -
          (frequency other : ℂ)) + (frequency other : ℂ)‖ := by ring_nf
    _ ≤ ‖(incrementFrequencyCoordinate axis frequency other : ℂ) -
          (frequency other : ℂ)‖ + ‖(frequency other : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + bound := add_le_add
      (norm_incrementFrequencyCoordinate_sub_le_one axis other frequency)
      (hfrequency other)
    _ = bound + 1 := by ring

/-- The frequency coordinate selected by the cross product against a basis input. -/
def hodgeCrossBasisFactor
    (frequency : SpatialFrequency) (component input : Fin 3) : ℂ :=
  complexCross (complexFrequencyVector frequency) (Pi.single input 1) component

/-- Every cross-basis factor is either zero or one signed frequency coordinate. -/
theorem norm_hodgeCrossBasisFactor_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (component input : Fin 3) :
    ‖hodgeCrossBasisFactor frequency component input‖ ≤ bound := by
  fin_cases component <;> fin_cases input <;>
    simp [hodgeCrossBasisFactor, complexCross, complexFrequencyVector,
      crossProduct] <;>
    first
    | simpa [Complex.norm_intCast] using hfrequency 0
    | simpa [Complex.norm_intCast] using hfrequency 1
    | simpa [Complex.norm_intCast] using hfrequency 2
    | exact hbound

/-- A cross-basis factor changes by norm at most one under a unit coordinate increment. -/
theorem norm_hodgeCrossBasisFactor_increment_sub_le_one
    (axis : Fin 3) (frequency : SpatialFrequency) (component input : Fin 3) :
    ‖hodgeCrossBasisFactor (incrementFrequencyCoordinate axis frequency) component input -
        hodgeCrossBasisFactor frequency component input‖ ≤ 1 := by
  fin_cases axis <;> fin_cases component <;> fin_cases input <;>
    simp [hodgeCrossBasisFactor, incrementFrequencyCoordinate,
      replaceFrequencyCoordinate, complexCross, complexFrequencyVector, crossProduct]

/-- The cross-basis factor remains bounded by `bound + 1` after a unit increment. -/
theorem norm_hodgeCrossBasisFactor_increment_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (axis component input : Fin 3) :
    ‖hodgeCrossBasisFactor (incrementFrequencyCoordinate axis frequency)
        component input‖ ≤ bound + 1 := by
  exact norm_hodgeCrossBasisFactor_le (by positivity)
    (incrementFrequencyCoordinate axis frequency)
    (norm_incrementFrequencyCoordinate_le hbound frequency hfrequency axis)
    component input

/-- The signed quadratic numerator in the exact Hodge ratio. -/
def hodgeJacobianRatioNumerator
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) : ℂ :=
  -((frequency coordinate : ℂ) *
    hodgeCrossBasisFactor frequency component input)

/-- The numerator bound already proved for the exact Hodge multiplier transfers to this chart. -/
theorem norm_hodgeJacobianRatioNumerator_le_frequencySquared
    (frequency : SpatialFrequency) (component coordinate input : Fin 3) :
    ‖hodgeJacobianRatioNumerator frequency component coordinate input‖ ≤
      frequencySquared frequency := by
  simpa [hodgeJacobianRatioNumerator, hodgeCrossBasisFactor] using
    norm_hodgeJacobianMultiplierNumerator_le_frequencySquared
      frequency component coordinate input

/-- A unit lattice increment changes the quadratic Hodge numerator by at most `2 bound + 1`. -/
theorem norm_hodgeJacobianRatioNumerator_increment_sub_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (axis component coordinate input : Fin 3) :
    ‖hodgeJacobianRatioNumerator (incrementFrequencyCoordinate axis frequency)
          component coordinate input -
        hodgeJacobianRatioNumerator frequency component coordinate input‖ ≤
      2 * bound + 1 := by
  let next := incrementFrequencyCoordinate axis frequency
  let a : ℂ := (frequency coordinate : ℂ)
  let aNext : ℂ := (next coordinate : ℂ)
  let b := hodgeCrossBasisFactor frequency component input
  let bNext := hodgeCrossBasisFactor next component input
  have ha : ‖a‖ ≤ bound := hfrequency coordinate
  have haDifference : ‖aNext - a‖ ≤ 1 :=
    norm_incrementFrequencyCoordinate_sub_le_one axis coordinate frequency
  have hbNext : ‖bNext‖ ≤ bound + 1 :=
    norm_hodgeCrossBasisFactor_increment_le hbound frequency hfrequency
      axis component input
  have hbDifference : ‖bNext - b‖ ≤ 1 :=
    norm_hodgeCrossBasisFactor_increment_sub_le_one
      axis frequency component input
  change ‖-(aNext * bNext) - -(a * b)‖ ≤ 2 * bound + 1
  calc
    ‖-(aNext * bNext) - -(a * b)‖ =
      ‖(aNext - a) * bNext + a * (bNext - b)‖ := by
        rw [show -(aNext * bNext) - -(a * b) =
          -((aNext - a) * bNext + a * (bNext - b)) by ring, norm_neg]
    _ ≤ ‖(aNext - a) * bNext‖ + ‖a * (bNext - b)‖ := norm_add_le _ _
    _ = ‖aNext - a‖ * ‖bNext‖ + ‖a‖ * ‖bNext - b‖ := by
      simp only [norm_mul]
    _ ≤ 1 * (bound + 1) + bound * 1 := by gcongr
    _ = 2 * bound + 1 := by ring

/-- The quadratic denominator changes by at most `2 bound + 1` under a unit increment. -/
theorem abs_frequencySquared_increment_sub_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (axis : Fin 3) :
    |frequencySquared (incrementFrequencyCoordinate axis frequency) -
        frequencySquared frequency| ≤
      2 * bound + 1 := by
  have haxis : |(frequency axis : ℝ)| ≤ bound := by
    simpa [Complex.norm_intCast] using hfrequency axis
  have hchange :
      frequencySquared (incrementFrequencyCoordinate axis frequency) -
          frequencySquared frequency =
        2 * (frequency axis : ℝ) + 1 := by
    rw [frequencySquared_incrementFrequencyCoordinate]
    ring
  rw [hchange]
  calc
    |2 * (frequency axis : ℝ) + 1| ≤
        |2 * (frequency axis : ℝ)| + |(1 : ℝ)| := abs_add_le _ _
    _ = 2 * |(frequency axis : ℝ)| + 1 := by
      rw [abs_one, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ 2 * bound + 1 := by gcongr
    _ = 2 * bound + 1 := by ring

/-- A quotient-difference receiver with real positive denominators.  It retains the numerator
change and denominator change as separate caused terms. -/
theorem norm_div_real_sub_div_real_le
    (firstNumerator nextNumerator : ℂ)
    (firstDenominator nextDenominator numeratorChange denominatorChange : ℝ)
    (hfirstDenominator : 0 < firstDenominator)
    (hnextDenominator : 0 < nextDenominator)
    (hnumeratorChange : 0 ≤ numeratorChange)
    (hdenominatorChange : 0 ≤ denominatorChange)
    (hfirstNumerator : ‖firstNumerator‖ ≤ firstDenominator)
    (hnumerator : ‖nextNumerator - firstNumerator‖ ≤ numeratorChange)
    (hdenominator : |nextDenominator - firstDenominator| ≤ denominatorChange) :
    ‖nextNumerator / (nextDenominator : ℂ) -
        firstNumerator / (firstDenominator : ℂ)‖ ≤
      (numeratorChange + denominatorChange) / nextDenominator := by
  have hfirstNe : (firstDenominator : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hfirstDenominator.ne'
  have hnextNe : (nextDenominator : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnextDenominator.ne'
  have hidentity :
      nextNumerator / (nextDenominator : ℂ) -
          firstNumerator / (firstDenominator : ℂ) =
        (nextNumerator - firstNumerator) / (nextDenominator : ℂ) +
          firstNumerator * ((firstDenominator - nextDenominator : ℝ) : ℂ) /
            ((nextDenominator : ℂ) * (firstDenominator : ℂ)) := by
    field_simp [hfirstNe, hnextNe]
    push_cast
    ring
  rw [hidentity]
  calc
    ‖(nextNumerator - firstNumerator) / (nextDenominator : ℂ) +
        firstNumerator * ((firstDenominator - nextDenominator : ℝ) : ℂ) /
          ((nextDenominator : ℂ) * (firstDenominator : ℂ))‖ ≤
      ‖(nextNumerator - firstNumerator) / (nextDenominator : ℂ)‖ +
        ‖firstNumerator * ((firstDenominator - nextDenominator : ℝ) : ℂ) /
          ((nextDenominator : ℂ) * (firstDenominator : ℂ))‖ := norm_add_le _ _
    _ = ‖nextNumerator - firstNumerator‖ / nextDenominator +
        ‖firstNumerator‖ * |firstDenominator - nextDenominator| /
          (nextDenominator * firstDenominator) := by
      simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hnextDenominator,
        abs_of_pos hfirstDenominator,
        abs_of_pos (mul_pos hnextDenominator hfirstDenominator)]
    _ ≤ numeratorChange / nextDenominator +
        firstDenominator * denominatorChange /
          (nextDenominator * firstDenominator) := by
      gcongr
      simpa only [abs_sub_comm] using hdenominator
    _ = (numeratorChange + denominatorChange) / nextDenominator := by
      field_simp [hfirstDenominator.ne', hnextDenominator.ne']

/-- First finite difference of an actual Hodge entry on the localized annulus.  The estimate has
the correct reciprocal-radius scale once `bound` is chosen as the adjacent outer radius. -/
theorem norm_hodgeJacobianMultiplierEntry_increment_sub_le
    (radius : ℕ) {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (axis component coordinate input : Fin 3)
    (hcurrent : frequency ∉ frequencyCube (radius + 1))
    (hnext : incrementFrequencyCoordinate axis frequency ∉ frequencyCube (radius + 1)) :
    ‖hodgeJacobianMultiplierEntry (incrementFrequencyCoordinate axis frequency)
          component coordinate input -
        hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      (4 * bound + 2) / (radius + 2 : ℝ) ^ 2 := by
  let next := incrementFrequencyCoordinate axis frequency
  let firstNumerator := hodgeJacobianRatioNumerator frequency component coordinate input
  let nextNumerator := hodgeJacobianRatioNumerator next component coordinate input
  let firstDenominator := frequencySquared frequency
  let nextDenominator := frequencySquared next
  have hfirstLower :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hcurrent
  have hnextLower :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hnext
  have hfirstPositive : 0 < firstDenominator := by
    exact (show 0 < (radius + 2 : ℝ) ^ 2 by positivity).trans_le hfirstLower
  have hnextPositive : 0 < nextDenominator := by
    exact (show 0 < (radius + 2 : ℝ) ^ 2 by positivity).trans_le hnextLower
  have hfirstNumerator : ‖firstNumerator‖ ≤ firstDenominator :=
    norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input
  have hnumerator : ‖nextNumerator - firstNumerator‖ ≤ 2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_increment_sub_le hbound frequency hfrequency
      axis component coordinate input
  have hdenominator : |nextDenominator - firstDenominator| ≤ 2 * bound + 1 :=
    abs_frequencySquared_increment_sub_le hbound frequency hfrequency axis
  have hratio := norm_div_real_sub_div_real_le
    firstNumerator nextNumerator firstDenominator nextDenominator
    (2 * bound + 1) (2 * bound + 1)
    hfirstPositive hnextPositive (by positivity) (by positivity)
    hfirstNumerator hnumerator hdenominator
  have hentries :
      hodgeJacobianMultiplierEntry next component coordinate input =
          nextNumerator / (nextDenominator : ℂ) ∧
        hodgeJacobianMultiplierEntry frequency component coordinate input =
          firstNumerator / (firstDenominator : ℂ) := by
    constructor
    · exact hodgeJacobianMultiplierEntry_eq_ratio
        next component coordinate input
    · exact hodgeJacobianMultiplierEntry_eq_ratio
        frequency component coordinate input
  rw [hentries.1, hentries.2]
  calc
    ‖nextNumerator / (nextDenominator : ℂ) -
        firstNumerator / (firstDenominator : ℂ)‖ ≤
      ((2 * bound + 1) + (2 * bound + 1)) / nextDenominator := hratio
    _ = (4 * bound + 2) / nextDenominator := by ring
    _ ≤ (4 * bound + 2) / (radius + 2 : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hnextLower

/-- Cube membership supplies the coordinate norm bound used by the rational variation theorem. -/
theorem norm_coordinate_le_of_mem_frequencyCube
    (cubeRadius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube cubeRadius) (axis : Fin 3) :
    ‖(frequency axis : ℂ)‖ ≤ cubeRadius := by
  have hnatAbs : (frequency axis).natAbs ≤ cubeRadius :=
    (natAbs_le_iff_bounds cubeRadius (frequency axis)).mpr
      ((mem_frequencyCube_iff cubeRadius frequency).mp hfrequency axis)
  have hcast : ((frequency axis).natAbs : ℝ) ≤ (cubeRadius : ℝ) := by
    exact_mod_cast hnatAbs
  simpa [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs] using hcast

/-- On the actual adjacent outer cube, the first Hodge difference is at most `8/(radius+2)`.
Both endpoints are required to lie outside the cancelled inner cube; crossing stencils are handled
by the exact plateau-zero theorem above instead of this quotient estimate. -/
theorem norm_hodgeJacobianMultiplierEntry_increment_sub_le_eight_div
    (radius : ℕ) (frequency : SpatialFrequency)
    (axis component coordinate input : Fin 3)
    (hcurrentOuter : frequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (hcurrentInner : frequency ∉ frequencyCube (radius + 1))
    (hnextOuter : incrementFrequencyCoordinate axis frequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (hnextInner : incrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1)) :
    ‖hodgeJacobianMultiplierEntry (incrementFrequencyCoordinate axis frequency)
          component coordinate input -
        hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      8 / (radius + 2 : ℝ) := by
  have hraw := norm_hodgeJacobianMultiplierEntry_increment_sub_le
    radius (bound := (valleePoussinOuterRadius (radius + 1) : ℝ))
    (by positivity) frequency
    (fun other ↦ norm_coordinate_le_of_mem_frequencyCube
      (valleePoussinOuterRadius (radius + 1)) hcurrentOuter other)
    axis component coordinate input hcurrentInner hnextInner
  refine hraw.trans ?_
  unfold valleePoussinOuterRadius
  have hdenominator : 0 < (radius + 2 : ℝ) := by positivity
  rw [div_le_iff₀ (sq_pos_of_pos hdenominator)]
  have hright :
      (8 / (radius + 2 : ℝ)) * (radius + 2 : ℝ) ^ 2 =
        8 * (radius + 2 : ℝ) := by
    field_simp [hdenominator.ne']
  rw [hright]
  push_cast
  nlinarith

/-! ## Second rational differences: polynomial data -/

/-- Two successive unit increments in the same addressed frequency coordinate. -/
def twiceIncrementFrequencyCoordinate
    (axis : Fin 3) (frequency : SpatialFrequency) : SpatialFrequency :=
  incrementFrequencyCoordinate axis (incrementFrequencyCoordinate axis frequency)

/-- Every coordinate chart is affine along a lattice coordinate line. -/
theorem incrementFrequencyCoordinate_coordinate_secondDifference_eq_zero
    (axis other : Fin 3) (frequency : SpatialFrequency) :
    (twiceIncrementFrequencyCoordinate axis frequency other : ℂ) -
        2 * (incrementFrequencyCoordinate axis frequency other : ℂ) +
          (frequency other : ℂ) = 0 := by
  fin_cases axis <;> fin_cases other <;>
    simp [twiceIncrementFrequencyCoordinate, incrementFrequencyCoordinate,
      replaceFrequencyCoordinate] <;>
    push_cast <;>
    ring

/-- Every cross-basis factor is likewise affine along a lattice coordinate line. -/
theorem hodgeCrossBasisFactor_secondDifference_eq_zero
    (axis : Fin 3) (frequency : SpatialFrequency) (component input : Fin 3) :
    hodgeCrossBasisFactor (twiceIncrementFrequencyCoordinate axis frequency)
        component input -
      2 * hodgeCrossBasisFactor (incrementFrequencyCoordinate axis frequency)
        component input +
      hodgeCrossBasisFactor frequency component input = 0 := by
  fin_cases axis <;> fin_cases component <;> fin_cases input <;>
    simp [hodgeCrossBasisFactor, twiceIncrementFrequencyCoordinate,
      incrementFrequencyCoordinate, replaceFrequencyCoordinate,
      complexCross, complexFrequencyVector, crossProduct] <;>
    push_cast <;>
    ring

/-- The signed quadratic Hodge numerator has second coordinate difference of norm at most two. -/
theorem norm_hodgeJacobianRatioNumerator_secondDifference_le_two
    (axis : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖hodgeJacobianRatioNumerator
          (twiceIncrementFrequencyCoordinate axis frequency)
          component coordinate input -
        2 * hodgeJacobianRatioNumerator
          (incrementFrequencyCoordinate axis frequency)
          component coordinate input +
        hodgeJacobianRatioNumerator frequency component coordinate input‖ ≤ 2 := by
  let next := incrementFrequencyCoordinate axis frequency
  let afterNext := twiceIncrementFrequencyCoordinate axis frequency
  let a0 : ℂ := (frequency coordinate : ℂ)
  let a1 : ℂ := (next coordinate : ℂ)
  let a2 : ℂ := (afterNext coordinate : ℂ)
  let b0 := hodgeCrossBasisFactor frequency component input
  let b1 := hodgeCrossBasisFactor next component input
  let b2 := hodgeCrossBasisFactor afterNext component input
  have haSecond : a2 - 2 * a1 + a0 = 0 :=
    incrementFrequencyCoordinate_coordinate_secondDifference_eq_zero
      axis coordinate frequency
  have hbSecond : b2 - 2 * b1 + b0 = 0 :=
    hodgeCrossBasisFactor_secondDifference_eq_zero axis frequency component input
  have haFirst : ‖a1 - a0‖ ≤ 1 :=
    norm_incrementFrequencyCoordinate_sub_le_one axis coordinate frequency
  have hbFirst : ‖b2 - b1‖ ≤ 1 :=
    norm_hodgeCrossBasisFactor_increment_sub_le_one axis next component input
  change ‖-(a2 * b2) - 2 * (-(a1 * b1)) + -(a0 * b0)‖ ≤ 2
  have hproduct : a2 * b2 - 2 * (a1 * b1) + a0 * b0 =
      2 * (a1 - a0) * (b2 - b1) := by
    rw [secondBackwardDifference_mul, haSecond, hbSecond]
    ring
  rw [show -(a2 * b2) - 2 * (-(a1 * b1)) + -(a0 * b0) =
    -(a2 * b2 - 2 * (a1 * b1) + a0 * b0) by ring,
    norm_neg, hproduct, norm_mul, norm_mul]
  have htwoNorm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwoNorm]
  nlinarith [norm_nonneg (a1 - a0), norm_nonneg (b2 - b1),
    mul_le_mul haFirst hbFirst (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)]

/-- The quadratic Hodge denominator has constant second coordinate difference exactly two. -/
theorem frequencySquared_secondDifference_eq_two
    (axis : Fin 3) (frequency : SpatialFrequency) :
    frequencySquared (twiceIncrementFrequencyCoordinate axis frequency) -
        2 * frequencySquared (incrementFrequencyCoordinate axis frequency) +
          frequencySquared frequency = 2 := by
  rw [twiceIncrementFrequencyCoordinate,
    frequencySquared_incrementFrequencyCoordinate,
    frequencySquared_incrementFrequencyCoordinate,
    incrementFrequencyCoordinate_apply_same]
  push_cast
  ring

/-! ## Second rational differences: reciprocal denominator -/

/-- Exact three-denominator identity for a second reciprocal difference. -/
theorem reciprocal_secondDifference_eq
    (first middle last : ℝ)
    (hfirst : first ≠ 0) (hmiddle : middle ≠ 0) (hlast : last ≠ 0) :
    1 / last - 2 / middle + 1 / first =
      -(last - 2 * middle + first) / (last * middle) +
        (middle - first) * (last - first) / (first * middle * last) := by
  field_simp [hfirst, hmiddle, hlast]
  ring

/-- Scale-separated norm bound for the reciprocal second difference.  `secondChange` measures
quadratic curvature of the denominator, while `firstChange` and `spanChange` retain the two
first-order passages. -/
theorem abs_reciprocal_secondDifference_le
    (first middle last lower firstChange spanChange secondChange : ℝ)
    (hlower : 0 < lower)
    (hfirstLower : lower ≤ first)
    (hmiddleLower : lower ≤ middle)
    (hlastLower : lower ≤ last)
    (hfirstChange : |middle - first| ≤ firstChange)
    (hspanChange : |last - first| ≤ spanChange)
    (hsecondChange : |last - 2 * middle + first| ≤ secondChange)
    (hfirstChangeNonneg : 0 ≤ firstChange)
    (hspanChangeNonneg : 0 ≤ spanChange)
    (hsecondChangeNonneg : 0 ≤ secondChange) :
    |1 / last - 2 / middle + 1 / first| ≤
      secondChange / lower ^ 2 +
        (firstChange * spanChange) / lower ^ 3 := by
  have hfirstPositive : 0 < first := hlower.trans_le hfirstLower
  have hmiddlePositive : 0 < middle := hlower.trans_le hmiddleLower
  have hlastPositive : 0 < last := hlower.trans_le hlastLower
  have htwoLower : lower ^ 2 ≤ last * middle := by
    rw [pow_two]
    exact mul_le_mul hlastLower hmiddleLower (le_of_lt hlower) (le_of_lt hlastPositive)
  have hthreeLower : lower ^ 3 ≤ first * middle * last := by
    rw [pow_succ, pow_two]
    exact mul_le_mul
      (mul_le_mul hfirstLower hmiddleLower (le_of_lt hlower)
        (le_of_lt hfirstPositive))
      hlastLower (le_of_lt hlower) (mul_nonneg (le_of_lt hfirstPositive)
        (le_of_lt hmiddlePositive))
  rw [reciprocal_secondDifference_eq first middle last
    hfirstPositive.ne' hmiddlePositive.ne' hlastPositive.ne']
  calc
    |-(last - 2 * middle + first) / (last * middle) +
        (middle - first) * (last - first) / (first * middle * last)| ≤
      |-(last - 2 * middle + first) / (last * middle)| +
        |(middle - first) * (last - first) / (first * middle * last)| :=
      abs_add_le _ _
    _ = |last - 2 * middle + first| / (last * middle) +
        (|middle - first| * |last - first|) / (first * middle * last) := by
      simp only [abs_div, abs_neg, abs_mul,
        abs_of_pos hfirstPositive, abs_of_pos hmiddlePositive,
        abs_of_pos hlastPositive]
    _ ≤ secondChange / lower ^ 2 +
        (firstChange * spanChange) / lower ^ 3 := by
      apply add_le_add
      · exact div_le_div₀ hsecondChangeNonneg hsecondChange
          (pow_pos hlower 2) htwoLower
      · have hproduct : |middle - first| * |last - first| ≤
            firstChange * spanChange :=
          mul_le_mul hfirstChange hspanChange (abs_nonneg _) hfirstChangeNonneg
        exact div_le_div₀ (mul_nonneg hfirstChangeNonneg hspanChangeNonneg)
          hproduct (pow_pos hlower 3) hthreeLower

/-- The reciprocal Hodge denominator has a sharp scale-separated second-difference estimate along
one lattice coordinate, provided all three stencil points lie outside the cancelled inner cube. -/
theorem abs_reciprocal_frequencySquared_secondDifference_le
    (radius : ℕ) {bound : ℝ} (hbound : 0 ≤ bound)
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hfirst : frequency ∉ frequencyCube (radius + 1))
    (hmiddle : incrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1))
    (hlast : twiceIncrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1)) :
    |1 / frequencySquared (twiceIncrementFrequencyCoordinate axis frequency) -
        2 / frequencySquared (incrementFrequencyCoordinate axis frequency) +
          1 / frequencySquared frequency| ≤
      2 / ((radius + 2 : ℝ) ^ 2) ^ 2 +
        ((2 * bound + 1) * (4 * bound + 4)) /
          ((radius + 2 : ℝ) ^ 2) ^ 3 := by
  let middleFrequency := incrementFrequencyCoordinate axis frequency
  let lastFrequency := twiceIncrementFrequencyCoordinate axis frequency
  let firstDenominator := frequencySquared frequency
  let middleDenominator := frequencySquared middleFrequency
  let lastDenominator := frequencySquared lastFrequency
  let lower := (radius + 2 : ℝ) ^ 2
  have hfirstLower : lower ≤ firstDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hfirst
  have hmiddleLower : lower ≤ middleDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hmiddle
  have hlastLower : lower ≤ lastDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hlast
  have hmiddleCoordinate : ∀ other : Fin 3,
      ‖(middleFrequency other : ℂ)‖ ≤ bound + 1 :=
    norm_incrementFrequencyCoordinate_le hbound frequency hfrequency axis
  have hfirstChange : |middleDenominator - firstDenominator| ≤ 2 * bound + 1 :=
    abs_frequencySquared_increment_sub_le hbound frequency hfrequency axis
  have hlastChange : |lastDenominator - middleDenominator| ≤ 2 * bound + 3 := by
    have hraw := abs_frequencySquared_increment_sub_le (bound := bound + 1)
      (by positivity) middleFrequency hmiddleCoordinate axis
    calc
      |lastDenominator - middleDenominator| =
          |frequencySquared (incrementFrequencyCoordinate axis middleFrequency) -
            frequencySquared middleFrequency| := by rfl
      _ ≤ 2 * (bound + 1) + 1 := hraw
      _ = 2 * bound + 3 := by ring
  have hspanChange : |lastDenominator - firstDenominator| ≤ 4 * bound + 4 := by
    calc
      |lastDenominator - firstDenominator| =
          |(lastDenominator - middleDenominator) +
            (middleDenominator - firstDenominator)| := by ring_nf
      _ ≤ |lastDenominator - middleDenominator| +
          |middleDenominator - firstDenominator| := abs_add_le _ _
      _ ≤ (2 * bound + 3) + (2 * bound + 1) :=
        add_le_add hlastChange hfirstChange
      _ = 4 * bound + 4 := by ring
  have hsecondChange :
      |lastDenominator - 2 * middleDenominator + firstDenominator| ≤ 2 := by
    rw [show lastDenominator - 2 * middleDenominator + firstDenominator = 2 by
      exact frequencySquared_secondDifference_eq_two axis frequency]
    norm_num
  exact abs_reciprocal_secondDifference_le
    firstDenominator middleDenominator lastDenominator lower
    (2 * bound + 1) (4 * bound + 4) 2
    (by positivity) hfirstLower hmiddleLower hlastLower
    hfirstChange hspanChange hsecondChange
    (by positivity) (by positivity) (by norm_num)

/-- An outer coordinate bound controls the full quadratic denominator by three times its square. -/
theorem frequencySquared_le_three_mul_sq
    {bound : ℝ} (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound) :
    frequencySquared frequency ≤ 3 * bound ^ 2 := by
  have hzero : |(frequency 0 : ℝ)| ≤ bound := by
    simpa [Complex.norm_intCast] using hfrequency 0
  have hone : |(frequency 1 : ℝ)| ≤ bound := by
    simpa [Complex.norm_intCast] using hfrequency 1
  have htwo : |(frequency 2 : ℝ)| ≤ bound := by
    simpa [Complex.norm_intCast] using hfrequency 2
  have hzeroSq : (frequency 0 : ℝ) ^ 2 ≤ bound ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hzero 2
    simpa only [sq_abs] using this
  have honeSq : (frequency 1 : ℝ) ^ 2 ≤ bound ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) hone 2
    simpa only [sq_abs] using this
  have htwoSq : (frequency 2 : ℝ) ^ 2 ≤ bound ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) htwo 2
    simpa only [sq_abs] using this
  simp [frequencySquared, Fin.sum_univ_succ]
  linarith

/-- Reciprocal first-difference control from a positive common lower denominator. -/
theorem abs_reciprocal_sub_le
    (first last lower change : ℝ)
    (hlower : 0 < lower) (hfirstLower : lower ≤ first)
    (hlastLower : lower ≤ last) (hchange : |last - first| ≤ change)
    (hchangeNonneg : 0 ≤ change) :
    |1 / last - 1 / first| ≤ change / lower ^ 2 := by
  have hfirstPositive : 0 < first := hlower.trans_le hfirstLower
  have hlastPositive : 0 < last := hlower.trans_le hlastLower
  have hidentity : 1 / last - 1 / first =
      (first - last) / (last * first) := by
    field_simp [hfirstPositive.ne', hlastPositive.ne']
  have hdenominator : lower ^ 2 ≤ last * first := by
    rw [pow_two]
    exact mul_le_mul hlastLower hfirstLower (le_of_lt hlower) (le_of_lt hlastPositive)
  rw [hidentity, abs_div, abs_of_pos (mul_pos hlastPositive hfirstPositive)]
  exact div_le_div₀ hchangeNonneg (by simpa only [abs_sub_comm] using hchange)
    (pow_pos hlower 2) hdenominator

/-- Fully localized second finite difference of one actual Hodge multiplier entry.  The displayed
bound is an explicit `O(radius⁻²)` expression when `bound` is the adjacent outer radius; no
coarse coefficient count enters. -/
theorem norm_hodgeJacobianMultiplierEntry_secondDifference_le
    (radius : ℕ) {bound : ℝ} (hbound : 0 ≤ bound)
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (component coordinate input : Fin 3)
    (hfirst : frequency ∉ frequencyCube (radius + 1))
    (hmiddle : incrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1))
    (hlast : twiceIncrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1)) :
    ‖hodgeJacobianMultiplierEntry (twiceIncrementFrequencyCoordinate axis frequency)
          component coordinate input -
        2 * hodgeJacobianMultiplierEntry (incrementFrequencyCoordinate axis frequency)
          component coordinate input +
        hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      2 / ((radius + 2 : ℝ) ^ 2) +
        2 * (2 * bound + 1) *
          ((2 * bound + 3) / ((radius + 2 : ℝ) ^ 2) ^ 2) +
        (3 * bound ^ 2) *
          (2 / ((radius + 2 : ℝ) ^ 2) ^ 2 +
            ((2 * bound + 1) * (4 * bound + 4)) /
              ((radius + 2 : ℝ) ^ 2) ^ 3) := by
  let middleFrequency := incrementFrequencyCoordinate axis frequency
  let lastFrequency := twiceIncrementFrequencyCoordinate axis frequency
  let firstNumerator := hodgeJacobianRatioNumerator frequency component coordinate input
  let middleNumerator := hodgeJacobianRatioNumerator middleFrequency component coordinate input
  let lastNumerator := hodgeJacobianRatioNumerator lastFrequency component coordinate input
  let firstDenominator := frequencySquared frequency
  let middleDenominator := frequencySquared middleFrequency
  let lastDenominator := frequencySquared lastFrequency
  let firstReciprocal : ℂ := 1 / (firstDenominator : ℂ)
  let middleReciprocal : ℂ := 1 / (middleDenominator : ℂ)
  let lastReciprocal : ℂ := 1 / (lastDenominator : ℂ)
  let lower := (radius + 2 : ℝ) ^ 2
  have hfirstLower : lower ≤ firstDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hfirst
  have hmiddleLower : lower ≤ middleDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hmiddle
  have hlastLower : lower ≤ lastDenominator :=
    radius_add_two_sq_le_frequencySquared_of_not_mem_inner radius hlast
  have hlowerPositive : 0 < lower := by positivity
  have hfirstPositive : 0 < firstDenominator := hlowerPositive.trans_le hfirstLower
  have hmiddlePositive : 0 < middleDenominator := hlowerPositive.trans_le hmiddleLower
  have hlastPositive : 0 < lastDenominator := hlowerPositive.trans_le hlastLower
  have hmiddleCoordinate : ∀ other : Fin 3,
      ‖(middleFrequency other : ℂ)‖ ≤ bound + 1 :=
    norm_incrementFrequencyCoordinate_le hbound frequency hfrequency axis
  have hlastDenominatorChange :
      |lastDenominator - middleDenominator| ≤ 2 * bound + 3 := by
    have hraw := abs_frequencySquared_increment_sub_le (bound := bound + 1)
      (by positivity) middleFrequency hmiddleCoordinate axis
    calc
      |lastDenominator - middleDenominator| =
          |frequencySquared (incrementFrequencyCoordinate axis middleFrequency) -
            frequencySquared middleFrequency| := by rfl
      _ ≤ 2 * (bound + 1) + 1 := hraw
      _ = 2 * bound + 3 := by ring
  have hlastReciprocalDifferenceReal :
      |1 / lastDenominator - 1 / middleDenominator| ≤
        (2 * bound + 3) / lower ^ 2 :=
    abs_reciprocal_sub_le middleDenominator lastDenominator lower
      (2 * bound + 3) hlowerPositive hmiddleLower hlastLower
      hlastDenominatorChange (by positivity)
  have hlastReciprocalDifference :
      ‖lastReciprocal - middleReciprocal‖ ≤
        (2 * bound + 3) / lower ^ 2 := by
    have hcast : lastReciprocal - middleReciprocal =
        ((1 / lastDenominator - 1 / middleDenominator : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hlastReciprocalDifferenceReal
  have hreciprocalSecondReal :
      |1 / lastDenominator - 2 / middleDenominator + 1 / firstDenominator| ≤
        2 / lower ^ 2 +
          ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3 :=
    abs_reciprocal_frequencySquared_secondDifference_le
      radius hbound axis frequency hfrequency hfirst hmiddle hlast
  have hreciprocalSecond :
      ‖lastReciprocal - 2 * middleReciprocal + firstReciprocal‖ ≤
        2 / lower ^ 2 +
          ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3 := by
    have hcast : lastReciprocal - 2 * middleReciprocal + firstReciprocal =
        ((1 / lastDenominator - 2 / middleDenominator +
          1 / firstDenominator : ℝ) : ℂ) := by
      simp [lastReciprocal, middleReciprocal, firstReciprocal, div_eq_mul_inv]
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    exact hreciprocalSecondReal
  have hlastReciprocal : ‖lastReciprocal‖ ≤ 1 / lower := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlastPositive]
    exact div_le_div_of_nonneg_left (by norm_num) hlowerPositive hlastLower
  have hnumeratorFirst : ‖middleNumerator - firstNumerator‖ ≤ 2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_increment_sub_le hbound frequency hfrequency
      axis component coordinate input
  have hnumeratorSecond :
      ‖lastNumerator - 2 * middleNumerator + firstNumerator‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_secondDifference_le_two
      axis frequency component coordinate input
  have hfirstNumerator : ‖firstNumerator‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hfrequency)
  have hproduct := norm_secondBackwardDifference_mul_le
    firstNumerator middleNumerator lastNumerator
    firstReciprocal middleReciprocal lastReciprocal
  have hentries :
      hodgeJacobianMultiplierEntry frequency component coordinate input =
          firstNumerator * firstReciprocal ∧
        hodgeJacobianMultiplierEntry middleFrequency component coordinate input =
          middleNumerator * middleReciprocal ∧
        hodgeJacobianMultiplierEntry lastFrequency component coordinate input =
          lastNumerator * lastReciprocal := by
    constructor
    · rw [hodgeJacobianMultiplierEntry_eq_ratio]
      simp [firstNumerator, firstReciprocal, hodgeJacobianRatioNumerator,
        hodgeCrossBasisFactor, firstDenominator, div_eq_mul_inv]
    · constructor
      · rw [hodgeJacobianMultiplierEntry_eq_ratio]
        simp [middleNumerator, middleReciprocal, hodgeJacobianRatioNumerator,
          hodgeCrossBasisFactor, middleDenominator, div_eq_mul_inv]
      · rw [hodgeJacobianMultiplierEntry_eq_ratio]
        simp [lastNumerator, lastReciprocal, hodgeJacobianRatioNumerator,
          hodgeCrossBasisFactor, lastDenominator, div_eq_mul_inv]
  rw [hentries.1, hentries.2.1, hentries.2.2]
  refine hproduct.trans ?_
  calc
    ‖lastNumerator - 2 * middleNumerator + firstNumerator‖ *
          ‖lastReciprocal‖ +
        2 * ‖middleNumerator - firstNumerator‖ *
          ‖lastReciprocal - middleReciprocal‖ +
        ‖firstNumerator‖ *
          ‖lastReciprocal - 2 * middleReciprocal + firstReciprocal‖ ≤
      2 * (1 / lower) +
        2 * (2 * bound + 1) * ((2 * bound + 3) / lower ^ 2) +
        (3 * bound ^ 2) *
          (2 / lower ^ 2 +
            ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) := by
      gcongr
    _ =
      2 / ((radius + 2 : ℝ) ^ 2) +
        2 * (2 * bound + 1) *
          ((2 * bound + 3) / ((radius + 2 : ℝ) ^ 2) ^ 2) +
        (3 * bound ^ 2) *
          (2 / ((radius + 2 : ℝ) ^ 2) ^ 2 +
            ((2 * bound + 1) * (4 * bound + 4)) /
              ((radius + 2 : ℝ) ^ 2) ^ 3) := by
      dsimp [lower]
      ring

/-- On the actual adjacent aperture, the localized rational Hodge curvature is bounded by a
single explicit reciprocal-square constant. -/
theorem norm_hodgeJacobianMultiplierEntry_secondDifference_le_442
    (radius : ℕ) (axis : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (houter : frequency ∈
      frequencyCube (valleePoussinOuterRadius (radius + 1)))
    (hfirst : frequency ∉ frequencyCube (radius + 1))
    (hmiddle : incrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1))
    (hlast : twiceIncrementFrequencyCoordinate axis frequency ∉
      frequencyCube (radius + 1)) :
    ‖hodgeJacobianMultiplierEntry (twiceIncrementFrequencyCoordinate axis frequency)
          component coordinate input -
        2 * hodgeJacobianMultiplierEntry (incrementFrequencyCoordinate axis frequency)
          component coordinate input +
        hodgeJacobianMultiplierEntry frequency component coordinate input‖ ≤
      442 / (radius + 2 : ℝ) ^ 2 := by
  have hraw := norm_hodgeJacobianMultiplierEntry_secondDifference_le
    radius (bound := (valleePoussinOuterRadius (radius + 1) : ℝ))
    (by positivity) axis frequency
    (fun other ↦ norm_coordinate_le_of_mem_frequencyCube
      (valleePoussinOuterRadius (radius + 1)) houter other)
    component coordinate input hfirst hmiddle hlast
  refine hraw.trans ?_
  unfold valleePoussinOuterRadius
  have hdenominator : 0 < (radius + 2 : ℝ) := by positivity
  apply (le_div_iff₀ (sq_pos_of_pos hdenominator)).mpr
  field_simp [hdenominator.ne']
  push_cast
  nlinarith [show (2 : ℝ) ≤ radius + 2 by norm_num]

/-! ## Summed zero-padded Leibniz receiver -/

/-- The shifted first-factor passage in the product rule is exactly the preceding first backward
difference, with an exact zero at the initial aperture point. -/
theorem zeroPaddedPrevious_sub_secondPrevious_eq
    (coefficient : ℕ → ℂ) (count index : ℕ) :
    zeroPaddedPreviousCoefficient coefficient count index -
        zeroPaddedSecondPreviousCoefficient coefficient count index =
      if index = 0 then 0 else
        zeroPaddedBackwardDifference coefficient count (index - 1) := by
  by_cases hzero : index = 0
  · subst index
    simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient]
  · rw [if_neg hzero]
    by_cases hone : index = 1
    · subst index
      simp [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
        zeroPaddedBackwardDifference]
    · have htwo : 2 ≤ index := by omega
      simp only [zeroPaddedPreviousCoefficient, zeroPaddedSecondPreviousCoefficient,
        zeroPaddedBackwardDifference, if_neg hzero,
        if_neg (show ¬index < 2 by omega),
        if_neg (show index - 1 ≠ 0 by omega)]
      rw [show index - 1 - 1 = index - 2 by omega]

/-- Summing the shifted passage recovers exactly the total first variation. -/
theorem sum_norm_zeroPaddedPrevious_sub_secondPrevious
    (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedPreviousCoefficient coefficient count index -
        zeroPaddedSecondPreviousCoefficient coefficient count index‖) =
      ∑ index ∈ Finset.range (count + 1),
        ‖zeroPaddedBackwardDifference coefficient count index‖ := by
  simp_rw [zeroPaddedPrevious_sub_secondPrevious_eq]
  rw [show count + 2 = (count + 1) + 1 by omega, Finset.sum_range_succ']
  simp

/-- Summing the twice-shifted zero-padded population recovers exactly the raw coefficient mass. -/
theorem sum_norm_zeroPaddedSecondPreviousCoefficient
    (coefficient : ℕ → ℂ) (count : ℕ) :
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondPreviousCoefficient coefficient count index‖) =
      ∑ index ∈ Finset.range count, ‖coefficient index‖ := by
  rw [show count + 2 = 2 + count by omega, Finset.sum_range_add]
  have hshift :
      (∑ index ∈ Finset.range count,
        ‖zeroPaddedSecondPreviousCoefficient coefficient count (2 + index)‖) =
      ∑ index ∈ Finset.range count, ‖coefficient index‖ := by
    apply Finset.sum_congr rfl
    intro index hindex
    rw [Finset.mem_range] at hindex
    simp [zeroPaddedSecondPreviousCoefficient, zeroPaddedCoefficient,
      show ¬2 + index < 2 by omega, show 2 + index - 2 = index by omega,
      hindex]
  rw [hshift]
  norm_num [Finset.sum_range_succ, zeroPaddedSecondPreviousCoefficient]

/-- Total second variation of a pointwise product, expressed only through total scalar curvature,
total scalar first variation, raw scalar mass, and uniform zeroth/first/second variation bounds on
the second factor.  This is the exact comb interface used after splitting plateau, boundary, and
localized-rational stencils. -/
theorem sum_norm_zeroPaddedSecondDifference_mul_le
    (first second : ℕ → ℂ) (count : ℕ)
    (zerothBound firstBound secondBound : ℝ)
    (hzerothNonneg : 0 ≤ zerothBound)
    (hfirstNonneg : 0 ≤ firstBound)
    (hsecondNonneg : 0 ≤ secondBound)
    (hzeroth : ∀ index,
      ‖zeroPaddedCoefficient second count index‖ ≤ zerothBound)
    (hfirst : ∀ index,
      ‖zeroPaddedCoefficient second count index -
        zeroPaddedPreviousCoefficient second count index‖ ≤ firstBound)
    (hsecond : ∀ index,
      ‖zeroPaddedSecondDifference second count index‖ ≤ secondBound) :
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖) ≤
      zerothBound *
          (∑ index ∈ Finset.range (count + 2),
            ‖zeroPaddedSecondDifference first count index‖) +
        2 * firstBound *
          (∑ index ∈ Finset.range (count + 1),
            ‖zeroPaddedBackwardDifference first count index‖) +
        secondBound *
          (∑ index ∈ Finset.range count, ‖first index‖) := by
  calc
    (∑ index ∈ Finset.range (count + 2),
      ‖zeroPaddedSecondDifference
        (fun position ↦ first position * second position) count index‖) ≤
      ∑ index ∈ Finset.range (count + 2),
        (‖zeroPaddedSecondDifference first count index‖ * zerothBound +
          2 * ‖zeroPaddedPreviousCoefficient first count index -
            zeroPaddedSecondPreviousCoefficient first count index‖ * firstBound +
          ‖zeroPaddedSecondPreviousCoefficient first count index‖ * secondBound) := by
      apply Finset.sum_le_sum
      intro index _hindex
      refine (norm_zeroPaddedSecondDifference_mul_le first second count index).trans ?_
      gcongr
      · exact hzeroth index
      · exact hfirst index
      · exact hsecond index
    _ =
      zerothBound *
          (∑ index ∈ Finset.range (count + 2),
            ‖zeroPaddedSecondDifference first count index‖) +
        2 * firstBound *
          (∑ index ∈ Finset.range (count + 1),
            ‖zeroPaddedBackwardDifference first count index‖) +
        secondBound *
          (∑ index ∈ Finset.range count, ‖first index‖) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, ← Finset.sum_mul]
      have htwo :
          (∑ index ∈ Finset.range (count + 2),
            2 * ‖zeroPaddedPreviousCoefficient first count index -
              zeroPaddedSecondPreviousCoefficient first count index‖) =
            2 * ∑ index ∈ Finset.range (count + 2),
              ‖zeroPaddedPreviousCoefficient first count index -
                zeroPaddedSecondPreviousCoefficient first count index‖ := by
        rw [Finset.mul_sum]
      rw [htwo, sum_norm_zeroPaddedPrevious_sub_secondPrevious]
      rw [← Finset.sum_mul,
        sum_norm_zeroPaddedSecondPreviousCoefficient]
      ring

section Audit

#print axioms annularHodgeCubeCoefficient_eq_zero_of_index_bounds
#print axioms zeroPaddedSecondDifference_mul
#print axioms annularHodgeCubeSecondDifferenceFirst_eq_zero_of_stencil_mem_inner
#print axioms annularHodgeCubeSecondDifferenceFirst_eq_zero_at_zero_crossing
#print axioms norm_hodgeJacobianMultiplierEntry_increment_sub_le_eight_div
#print axioms norm_hodgeJacobianMultiplierEntry_secondDifference_le_442
#print axioms sum_norm_zeroPaddedSecondDifference_mul_le

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
