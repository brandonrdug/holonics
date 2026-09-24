import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeSupportStencil
import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

/-!
# Coordinatewise support pins for the three-axis dyadic Hodge stencil

A six-step `2 × 2 × 2` word is not six steps in any one lattice coordinate.  Because the
three axes are addressed and distinct, the coordinate which witnesses departure from the inner
cube moves by at most two.  This owner retains that typing and proves that the same
`(2^s - 3)^2` denominator used by the two-axis descent controls the complete three-axis
complementary stencil.  Collapsing the word to an untyped path length would lose this fact.

Truth status: `[proved-derived] [formal-checked]`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

/-- If every addressed point of a three-axis box vanishes, its mixed forward difference
vanishes. -/
theorem threeAxisMixedForwardDifference_eq_zero_of_stencil_eq_zero
    (firstOrder secondOrder thirdOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (hzero : ∀ firstIndex, firstIndex ≤ firstOrder →
      ∀ secondIndex, secondIndex ≤ secondOrder →
        ∀ thirdIndex, thirdIndex ≤ thirdOrder →
          coefficient (threeAxisStencilPoint 0 1 2 frequency
            firstIndex secondIndex thirdIndex) = 0) :
    threeAxisMixedForwardDifference 0 1 2 firstOrder secondOrder thirdOrder
      coefficient frequency = 0 := by
  unfold threeAxisMixedForwardDifference
  apply fwdDiff_iter_eq_zero_of_points
  intro firstIndex hfirstIndex
  apply fwdDiff_iter_eq_zero_of_points
  intro secondIndex hsecondIndex
  apply fwdDiff_iter_eq_zero_of_points
  intro thirdIndex hthirdIndex
  have hpoint :
      frequency + firstIndex • coordinateStep 0 +
          secondIndex • coordinateStep 1 + thirdIndex • coordinateStep 2 =
        threeAxisStencilPoint 0 1 2 frequency
          firstIndex secondIndex thirdIndex := by
    rfl
  rw [hpoint]
  exact hzero firstIndex hfirstIndex secondIndex hsecondIndex thirdIndex hthirdIndex

/-- A nonzero three-axis scalar variation exposes one genuinely nonzero coefficient in its
addressed box. -/
theorem exists_nonzero_stencil_point_of_threeAxisMixedForwardDifference_ne_zero
    (firstOrder secondOrder thirdOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (hnonzero : threeAxisMixedForwardDifference 0 1 2
      firstOrder secondOrder thirdOrder coefficient frequency ≠ 0) :
    ∃ firstIndex, firstIndex ≤ firstOrder ∧
      ∃ secondIndex, secondIndex ≤ secondOrder ∧
        ∃ thirdIndex, thirdIndex ≤ thirdOrder ∧
          coefficient (threeAxisStencilPoint 0 1 2 frequency
            firstIndex secondIndex thirdIndex) ≠ 0 := by
  by_contra hnot
  push_neg at hnot
  exact hnonzero (threeAxisMixedForwardDifference_eq_zero_of_stencil_eq_zero
    firstOrder secondOrder thirdOrder coefficient frequency
      (fun firstIndex hfirstIndex secondIndex hsecondIndex thirdIndex hthirdIndex ↦
        hnot firstIndex hfirstIndex secondIndex hsecondIndex thirdIndex hthirdIndex))

/-- A nonzero direct-band scalar face contains a pin outside the cancelled inner cube and inside
the exact next-profile support cube. -/
theorem exists_directDyadicScalar_threeAxis_support_pin
    (scale firstOrder secondOrder thirdOrder : ℕ) (frequency : SpatialFrequency)
    (hnonzero : threeAxisMixedForwardDifference 0 1 2
      firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ∃ firstIndex, firstIndex ≤ firstOrder ∧
      ∃ secondIndex, secondIndex ≤ secondOrder ∧
        ∃ thirdIndex, thirdIndex ≤ thirdOrder ∧
          let pin := threeAxisStencilPoint 0 1 2 frequency
            firstIndex secondIndex thirdIndex
          pin ∉ frequencyCube (dyadicHodgeInnerCutoff scale) ∧
            pin ∈ frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
  obtain ⟨firstIndex, hfirstIndex, secondIndex, hsecondIndex,
      thirdIndex, hthirdIndex, hpin⟩ :=
    exists_nonzero_stencil_point_of_threeAxisMixedForwardDifference_ne_zero
      firstOrder secondOrder thirdOrder (directDyadicScalarCoefficient scale)
        frequency hnonzero
  refine ⟨firstIndex, hfirstIndex, secondIndex, hsecondIndex,
    thirdIndex, hthirdIndex, ?_, ?_⟩
  · intro hinner
    apply hpin
    simp [directDyadicScalarCoefficient,
      dyadicHodgeBandWeight_eq_zero_of_mem_inner scale hinner]
  · by_contra houter
    apply hpin
    simp [directDyadicScalarCoefficient,
      dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houter]

theorem threeAxisStencilPoint_zero_one_two_apply
    (axis : Fin 3) (frequency : SpatialFrequency) (first second third : ℕ) :
    threeAxisStencilPoint 0 1 2 frequency first second third axis =
      frequency axis +
        (if axis = 0 then (first : ℤ) else 0) +
        (if axis = 1 then (second : ℤ) else 0) +
        (if axis = 2 then (third : ℤ) else 0) := by
  fin_cases axis <;>
    simp [threeAxisStencilPoint, coordinateStep]

/-- Between two ordered points of the `2 × 2 × 2` box, each individual coordinate changes
by at most two even though the full chronological word has length six. -/
theorem exists_coordinate_offset_between_threeAxisStencilPoints
    (axis : Fin 3) (frequency : SpatialFrequency)
    (firstStart secondStart thirdStart firstEnd secondEnd thirdEnd : ℕ)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd)
    (hthird : thirdStart ≤ thirdEnd)
    (hfirstEnd : firstEnd ≤ 2) (hsecondEnd : secondEnd ≤ 2)
    (hthirdEnd : thirdEnd ≤ 2) :
    ∃ offset : ℕ, offset ≤ 2 ∧
      threeAxisStencilPoint 0 1 2 frequency firstEnd secondEnd thirdEnd axis =
        threeAxisStencilPoint 0 1 2 frequency firstStart secondStart thirdStart axis +
          (offset : ℤ) := by
  fin_cases axis
  · refine ⟨firstEnd - firstStart, by omega, ?_⟩
    rw [threeAxisStencilPoint_zero_one_two_apply,
      threeAxisStencilPoint_zero_one_two_apply]
    simp [Nat.cast_sub hfirst]
  · refine ⟨secondEnd - secondStart, by omega, ?_⟩
    rw [threeAxisStencilPoint_zero_one_two_apply,
      threeAxisStencilPoint_zero_one_two_apply]
    simp [Nat.cast_sub hsecond]
  · refine ⟨thirdEnd - thirdStart, by omega, ?_⟩
    rw [threeAxisStencilPoint_zero_one_two_apply,
      threeAxisStencilPoint_zero_one_two_apply]
    simp [Nat.cast_sub hthird]

/-- An outside-cube pin controls the quadratic denominator throughout the complete three-axis
box.  The proof uses the coordinatewise displacement bound rather than the six-letter word
length. -/
theorem radius_sub_three_sq_le_frequencySquared_of_threeAxis_support_pin
    (radius : ℕ) (hradius : 3 ≤ radius) (frequency : SpatialFrequency)
    (firstStart secondStart thirdStart firstEnd secondEnd thirdEnd : ℕ)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd)
    (hthird : thirdStart ≤ thirdEnd)
    (hfirstEnd : firstEnd ≤ 2) (hsecondEnd : secondEnd ≤ 2)
    (hthirdEnd : thirdEnd ≤ 2)
    (hpin : threeAxisStencilPoint 0 1 2 frequency
      firstStart secondStart thirdStart ∉ frequencyCube radius) :
    ((radius - 3 : ℕ) : ℝ) ^ 2 ≤
      frequencySquared
        (threeAxisStencilPoint 0 1 2 frequency firstEnd secondEnd thirdEnd) := by
  let start := threeAxisStencilPoint 0 1 2 frequency
    firstStart secondStart thirdStart
  let finish := threeAxisStencilPoint 0 1 2 frequency firstEnd secondEnd thirdEnd
  obtain ⟨axis, haxis⟩ :=
    exists_coordinate_natAbs_ge_of_not_mem_frequencyCube radius hpin
  obtain ⟨offset, hoffset, hfinish⟩ :=
    exists_coordinate_offset_between_threeAxisStencilPoints axis frequency
      firstStart secondStart thirdStart firstEnd secondEnd thirdEnd
      hfirst hsecond hthird hfirstEnd hsecondEnd hthirdEnd
  have htriangle : (start axis).natAbs ≤ (finish axis).natAbs + offset := by
    have hstart : start axis = finish axis + (-(offset : ℤ)) := by
      dsimp [start, finish] at hfinish ⊢
      omega
    rw [hstart]
    simpa using Int.natAbs_add_le (finish axis) (-(offset : ℤ))
  have hfinishAbs : radius - 3 ≤ (finish axis).natAbs := by
    dsimp [start] at haxis htriangle
    omega
  have hcast : ((radius - 3 : ℕ) : ℝ) ≤ |(finish axis : ℝ)| := by
    have hcast' : ((radius - 3 : ℕ) : ℝ) ≤ ((finish axis).natAbs : ℝ) := by
      exact_mod_cast hfinishAbs
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast'
  have hsquare : ((radius - 3 : ℕ) : ℝ) ^ 2 ≤ (finish axis : ℝ) ^ 2 := by
    have hsquareAbs := pow_le_pow_left₀ (by positivity) hcast 2
    simpa only [sq_abs] using hsquareAbs
  have hterm : (finish axis : ℝ) ^ 2 ≤ frequencySquared finish := by
    unfold frequencySquared
    exact Finset.single_le_sum
      (fun other _hother ↦ sq_nonneg (finish other : ℝ)) (Finset.mem_univ axis)
  exact hsquare.trans hterm

/-- The same pin controls the upper coordinate aperture. -/
theorem norm_threeAxisStencilPoint_le_outer_add_four_of_support_pin
    (outer : ℕ) (frequency : SpatialFrequency)
    (firstStart secondStart thirdStart firstEnd secondEnd thirdEnd : ℕ)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd)
    (hthird : thirdStart ≤ thirdEnd)
    (hfirstEnd : firstEnd ≤ 2) (hsecondEnd : secondEnd ≤ 2)
    (hthirdEnd : thirdEnd ≤ 2)
    (hpin : threeAxisStencilPoint 0 1 2 frequency
      firstStart secondStart thirdStart ∈ frequencyCube outer)
    (axis : Fin 3) :
    ‖(threeAxisStencilPoint 0 1 2 frequency firstEnd secondEnd thirdEnd axis : ℂ)‖ ≤
      (outer + 4 : ℝ) := by
  let start := threeAxisStencilPoint 0 1 2 frequency
    firstStart secondStart thirdStart
  let finish := threeAxisStencilPoint 0 1 2 frequency firstEnd secondEnd thirdEnd
  obtain ⟨offset, hoffset, hfinish⟩ :=
    exists_coordinate_offset_between_threeAxisStencilPoints axis frequency
      firstStart secondStart thirdStart firstEnd secondEnd thirdEnd
      hfirst hsecond hthird hfirstEnd hsecondEnd hthirdEnd
  have hstart : (start axis).natAbs ≤ outer := by
    rw [mem_frequencyCube_iff] at hpin
    exact (natAbs_le_iff_bounds outer (start axis)).mpr (hpin axis)
  have htriangle : (finish axis).natAbs ≤ (start axis).natAbs + offset := by
    dsimp [start, finish] at hfinish ⊢
    rw [hfinish]
    simpa using Int.natAbs_add_le (start axis) (offset : ℤ)
  have hnat : (finish axis).natAbs ≤ outer + 4 := by omega
  have hcast : ((finish axis).natAbs : ℝ) ≤ (outer + 4 : ℝ) := by
    exact_mod_cast hnat
  simpa [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs] using hcast

/-- **Three-axis complementary-stencil receiver.**  Every nonzero scalar allocation face of the
direct dyadic band controls its genuine Hodge complement on the complete shifted box. -/
theorem directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil
    (scale firstOrder secondOrder thirdOrder : ℕ)
    (hscale : 3 ≤ dyadicHodgeInnerCutoff scale)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (hthirdOrder : thirdOrder ≤ 2) (frequency : SpatialFrequency)
    (hnonzero : threeAxisMixedForwardDifference 0 1 2
      firstOrder secondOrder thirdOrder
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ThreeAxisStencilControlled
      (((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) ^ 2)
      (dyadicHodgeOuterCutoff (scale + 1) + 4 : ℝ)
      0 1 2
      (threeAxisStencilPoint 0 1 2 frequency firstOrder secondOrder thirdOrder)
      (2 - firstOrder) (2 - secondOrder) (2 - thirdOrder) := by
  obtain ⟨firstPin, hfirstPin, secondPin, hsecondPin, thirdPin, hthirdPin,
      hpinInner, hpinOuter⟩ :=
    exists_directDyadicScalar_threeAxis_support_pin
      scale firstOrder secondOrder thirdOrder frequency hnonzero
  intro firstIndex hfirstIndex secondIndex hsecondIndex thirdIndex hthirdIndex
  have hfirstEnd : firstOrder + firstIndex ≤ 2 := by omega
  have hsecondEnd : secondOrder + secondIndex ≤ 2 := by omega
  have hthirdEnd : thirdOrder + thirdIndex ≤ 2 := by omega
  have hpoint :
      threeAxisStencilPoint 0 1 2
          (threeAxisStencilPoint 0 1 2 frequency
            firstOrder secondOrder thirdOrder)
          firstIndex secondIndex thirdIndex =
        threeAxisStencilPoint 0 1 2 frequency
          (firstOrder + firstIndex) (secondOrder + secondIndex)
          (thirdOrder + thirdIndex) := by
    unfold threeAxisStencilPoint
    rw [add_nsmul, add_nsmul, add_nsmul]
    abel
  rw [hpoint]
  constructor
  · exact radius_sub_three_sq_le_frequencySquared_of_threeAxis_support_pin
      (dyadicHodgeInnerCutoff scale) hscale frequency
      firstPin secondPin thirdPin
      (firstOrder + firstIndex) (secondOrder + secondIndex) (thirdOrder + thirdIndex)
      (by omega) (by omega) (by omega) hfirstEnd hsecondEnd hthirdEnd hpinInner
  · intro axis
    exact norm_threeAxisStencilPoint_le_outer_add_four_of_support_pin
      (dyadicHodgeOuterCutoff (scale + 1)) frequency
      firstPin secondPin thirdPin
      (firstOrder + firstIndex) (secondOrder + secondIndex) (thirdOrder + thirdIndex)
      (by omega) (by omega) (by omega) hfirstEnd hsecondEnd hthirdEnd hpinOuter axis

section Audit

#print axioms exists_directDyadicScalar_threeAxis_support_pin
#print axioms radius_sub_three_sq_le_frequencySquared_of_threeAxis_support_pin
#print axioms directDyadicScalar_threeAxis_support_controls_complementaryHodgeStencil

end Audit

end Soma.Holonics.Millennium.NavierStokesThreeAxisDyadicHodgeSupportStencil
