import ElementaryHolonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation

/-!
# Support witnesses for direct dyadic Hodge stencils

**[proved-derived]** A nonzero mixed difference of the direct scalar band contains an actual
nonzero band pin.  That pin lies outside the cancelled inner cube and inside the genuine outer
support.  The resulting addressed witness controls every complementary Hodge stencil without
discarding zero-crossing or aperture faces.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeKernelVariation
open Soma.Holonics.Millennium.NavierStokesDyadicTensorBandSubsetVariation

/-! ## A mixed difference retains an actual support pin -/

theorem fwdDiff_iter_eq_zero_of_points
    (step : SpatialFrequency) (coefficient : SpatialFrequency → ℂ)
    (order : ℕ) (frequency : SpatialFrequency)
    (hzero : ∀ index, index ≤ order →
      coefficient (frequency + index • step) = 0) :
    (fwdDiff step)^[order] coefficient frequency = 0 := by
  induction order generalizing frequency with
  | zero =>
      simpa using hzero 0 (by omega)
  | succ order inductionHypothesis =>
      have hcurrent := inductionHypothesis frequency fun index hindex ↦
        hzero index (by omega)
      have hnext := inductionHypothesis (frequency + step) fun index hindex ↦ by
        rw [show frequency + step + index • step =
          frequency + (index + 1) • step by
            rw [add_nsmul]
            simp only [one_nsmul]
            abel]
        exact hzero (index + 1) (by omega)
      simp only [Function.iterate_succ_apply', fwdDiff]
      rw [hcurrent, hnext, sub_zero]

theorem mixedForwardDifference_eq_zero_of_stencil_eq_zero
    (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (hzero : ∀ firstIndex, firstIndex ≤ firstOrder →
      ∀ secondIndex, secondIndex ≤ secondOrder →
        coefficient (twoAxisStencilPoint first second frequency
          firstIndex secondIndex) = 0) :
    mixedForwardDifference first second firstOrder secondOrder
      coefficient frequency = 0 := by
  unfold mixedForwardDifference
  apply fwdDiff_iter_eq_zero_of_points
  intro firstIndex hfirstIndex
  apply fwdDiff_iter_eq_zero_of_points
  intro secondIndex hsecondIndex
  have hpoint :
      frequency + firstIndex • coordinateStep first +
          secondIndex • coordinateStep second =
        twoAxisStencilPoint first second frequency firstIndex secondIndex := by
    rfl
  rw [hpoint]
  exact hzero firstIndex hfirstIndex secondIndex hsecondIndex

/-- Nonzero mixed variation exposes one genuinely nonzero coefficient in its addressed
rectangle. -/
theorem exists_nonzero_stencil_point_of_mixedForwardDifference_ne_zero
    (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) (frequency : SpatialFrequency)
    (hnonzero : mixedForwardDifference first second firstOrder secondOrder
      coefficient frequency ≠ 0) :
    ∃ firstIndex, firstIndex ≤ firstOrder ∧
      ∃ secondIndex, secondIndex ≤ secondOrder ∧
        coefficient (twoAxisStencilPoint first second frequency
          firstIndex secondIndex) ≠ 0 := by
  by_contra hnot
  push_neg at hnot
  exact hnonzero (mixedForwardDifference_eq_zero_of_stencil_eq_zero
    first second firstOrder secondOrder coefficient frequency
      (fun firstIndex hfirstIndex secondIndex hsecondIndex ↦
        hnot firstIndex hfirstIndex secondIndex hsecondIndex))

def directDyadicScalarCoefficient (scale : ℕ) (frequency : SpatialFrequency) : ℂ :=
  (dyadicHodgeBandWeight scale frequency : ℂ)

/-- A nonzero scalar subset face contains a pin outside the cancelled inner cube and inside the
next profile's exact support cube. -/
theorem exists_directDyadicScalar_support_pin
    (scale : ℕ) (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (frequency : SpatialFrequency)
    (hnonzero : mixedForwardDifference first second firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    ∃ firstIndex, firstIndex ≤ firstOrder ∧
      ∃ secondIndex, secondIndex ≤ secondOrder ∧
        let pin := twoAxisStencilPoint first second frequency firstIndex secondIndex
        pin ∉ frequencyCube (dyadicHodgeInnerCutoff scale) ∧
          pin ∈ frequencyCube (dyadicHodgeOuterCutoff (scale + 1)) := by
  obtain ⟨firstIndex, hfirstIndex, secondIndex, hsecondIndex, hpin⟩ :=
    exists_nonzero_stencil_point_of_mixedForwardDifference_ne_zero
      first second firstOrder secondOrder (directDyadicScalarCoefficient scale)
        frequency hnonzero
  refine ⟨firstIndex, hfirstIndex, secondIndex, hsecondIndex, ?_, ?_⟩
  · intro hinner
    apply hpin
    simp [directDyadicScalarCoefficient,
      dyadicHodgeBandWeight_eq_zero_of_mem_inner scale hinner]
  · by_contra houter
    apply hpin
    simp [directDyadicScalarCoefficient,
      dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale houter]

/-! ## Coordinate transport from the support pin -/

theorem twoAxisStencilPoint_apply
    (first second axis : Fin 3) (frequency : SpatialFrequency)
    (firstIndex secondIndex : ℕ) :
    twoAxisStencilPoint first second frequency firstIndex secondIndex axis =
      frequency axis +
        (if axis = first then (firstIndex : ℤ) else 0) +
        (if axis = second then (secondIndex : ℤ) else 0) := by
  unfold twoAxisStencilPoint coordinateStep
  by_cases hfirst : axis = first <;>
    by_cases hsecond : axis = second <;>
      simp [hfirst, hsecond, Pi.single_apply]

/-- Moving forward inside a two-axis rectangle adds a nonnegative coordinate offset bounded by
the total address displacement. -/
theorem exists_coordinate_offset_between_twoAxisStencilPoints
    (first second axis : Fin 3) (frequency : SpatialFrequency)
    (firstStart secondStart firstEnd secondEnd : ℕ)
    (haxes : first ≠ second)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd) :
    ∃ offset : ℕ,
      offset ≤ (firstEnd - firstStart) + (secondEnd - secondStart) ∧
      twoAxisStencilPoint first second frequency firstEnd secondEnd axis =
        twoAxisStencilPoint first second frequency firstStart secondStart axis +
          (offset : ℤ) := by
  let offset :=
    (if axis = first then firstEnd - firstStart else 0) +
      (if axis = second then secondEnd - secondStart else 0)
  refine ⟨offset, ?_, ?_⟩
  · dsimp [offset]
    split_ifs <;> omega
  · rw [twoAxisStencilPoint_apply, twoAxisStencilPoint_apply]
    dsimp [offset]
    by_cases haxisFirst : axis = first <;>
      by_cases haxisSecond : axis = second <;>
        simp [haxisFirst, haxisSecond, haxes, haxes.symm,
          Nat.cast_sub hfirst, Nat.cast_sub hsecond]

theorem exists_coordinate_natAbs_ge_of_not_mem_frequencyCube
    (radius : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉ frequencyCube radius) :
    ∃ axis : Fin 3, radius + 1 ≤ (frequency axis).natAbs := by
  by_contra hnot
  push_neg at hnot
  apply hfrequency
  rw [mem_frequencyCube_iff]
  intro axis
  apply (natAbs_le_iff_bounds radius (frequency axis)).mp
  have haxis := hnot axis
  omega

/-- A support pin outside radius `N` controls every later point at total address distance at most
four by the genuine lower scale `(N-3)^2`. -/
theorem radius_sub_three_sq_le_frequencySquared_of_support_pin
    (radius : ℕ) (hradius : 3 ≤ radius)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (firstStart secondStart firstEnd secondEnd : ℕ)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd)
    (hdistance : (firstEnd - firstStart) + (secondEnd - secondStart) ≤ 4)
    (hpin : twoAxisStencilPoint first second frequency firstStart secondStart ∉
      frequencyCube radius) :
    ((radius - 3 : ℕ) : ℝ) ^ 2 ≤
      frequencySquared
        (twoAxisStencilPoint first second frequency firstEnd secondEnd) := by
  let start := twoAxisStencilPoint first second frequency firstStart secondStart
  let finish := twoAxisStencilPoint first second frequency firstEnd secondEnd
  obtain ⟨axis, haxis⟩ :=
    exists_coordinate_natAbs_ge_of_not_mem_frequencyCube radius hpin
  obtain ⟨offset, hoffset, hfinish⟩ :=
    exists_coordinate_offset_between_twoAxisStencilPoints
      first second axis frequency firstStart secondStart firstEnd secondEnd
        haxes hfirst hsecond
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

/-- The same support pin controls the coordinate aperture of every later point by the true outer
support radius plus the four-step product stencil. -/
theorem norm_twoAxisStencilPoint_le_outer_add_four_of_support_pin
    (outer : ℕ) (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (firstStart secondStart firstEnd secondEnd : ℕ)
    (hfirst : firstStart ≤ firstEnd) (hsecond : secondStart ≤ secondEnd)
    (hdistance : (firstEnd - firstStart) + (secondEnd - secondStart) ≤ 4)
    (hpin : twoAxisStencilPoint first second frequency firstStart secondStart ∈
      frequencyCube outer)
    (axis : Fin 3) :
    ‖(twoAxisStencilPoint first second frequency firstEnd secondEnd axis : ℂ)‖ ≤
      (outer + 4 : ℝ) := by
  let start := twoAxisStencilPoint first second frequency firstStart secondStart
  let finish := twoAxisStencilPoint first second frequency firstEnd secondEnd
  obtain ⟨offset, hoffset, hfinish⟩ :=
    exists_coordinate_offset_between_twoAxisStencilPoints
      first second axis frequency firstStart secondStart firstEnd secondEnd
        haxes hfirst hsecond
  have hstart : (start axis).natAbs ≤ outer := by
    rw [mem_frequencyCube_iff] at hpin
    exact (natAbs_le_iff_bounds outer (start axis)).mpr (hpin axis)
  have htriangle : (finish axis).natAbs ≤ (start axis).natAbs + offset := by
    dsimp [start, finish] at hfinish ⊢
    rw [hfinish]
    simpa using Int.natAbs_add_le
      (twoAxisStencilPoint first second frequency firstStart secondStart axis)
      (offset : ℤ)
  have hnat : (finish axis).natAbs ≤ outer + 4 := by omega
  have hcast : ((finish axis).natAbs : ℝ) ≤ (outer + 4 : ℝ) := by
    exact_mod_cast hnat
  simpa [Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs] using hcast

/-- **Complementary-stencil receiver.** Every nonzero scalar `(a,b)` face of the direct dyadic
band controls the genuine Hodge `(2-a,2-b)` stencil at the shifted product-rule address.  The
lower denominator is `(2^s-3)^2`; the coordinate aperture is the exact next support plus four.
Zero crossings and both support boundaries remain in the addressed witness. -/
theorem directDyadicScalar_support_controls_complementaryHodgeStencil
    (scale : ℕ)
    (hscale : 3 ≤ dyadicHodgeInnerCutoff scale)
    (first second : Fin 3) (haxes : first ≠ second)
    (firstOrder secondOrder : ℕ)
    (hfirstOrder : firstOrder ≤ 2) (hsecondOrder : secondOrder ≤ 2)
    (frequency : SpatialFrequency)
    (hnonzero : mixedForwardDifference first second firstOrder secondOrder
      (directDyadicScalarCoefficient scale) frequency ≠ 0) :
    TwoAxisStencilControlled
      (((dyadicHodgeInnerCutoff scale - 3 : ℕ) : ℝ) ^ 2)
      (dyadicHodgeOuterCutoff (scale + 1) + 4 : ℝ)
      first second
      (twoAxisStencilPoint first second frequency firstOrder secondOrder)
      (2 - firstOrder) (2 - secondOrder) := by
  obtain ⟨firstPin, hfirstPin, secondPin, hsecondPin,
      hpinInner, hpinOuter⟩ :=
    exists_directDyadicScalar_support_pin scale first second
      firstOrder secondOrder frequency hnonzero
  intro firstIndex hfirstIndex secondIndex hsecondIndex
  have hfirstEnd : firstOrder + firstIndex ≤ 2 := by omega
  have hsecondEnd : secondOrder + secondIndex ≤ 2 := by omega
  have hfirstStart : firstPin ≤ firstOrder + firstIndex := by omega
  have hsecondStart : secondPin ≤ secondOrder + secondIndex := by omega
  have hdistance :
      (firstOrder + firstIndex - firstPin) +
        (secondOrder + secondIndex - secondPin) ≤ 4 := by omega
  have hpoint :
      twoAxisStencilPoint first second
          (twoAxisStencilPoint first second frequency firstOrder secondOrder)
          firstIndex secondIndex =
        twoAxisStencilPoint first second frequency
          (firstOrder + firstIndex) (secondOrder + secondIndex) :=
    twoAxisStencilPoint_rebase first second frequency
      firstOrder secondOrder firstIndex secondIndex
  constructor
  · rw [hpoint]
    exact radius_sub_three_sq_le_frequencySquared_of_support_pin
      (dyadicHodgeInnerCutoff scale) hscale first second haxes frequency
        firstPin secondPin (firstOrder + firstIndex) (secondOrder + secondIndex)
        hfirstStart hsecondStart hdistance hpinInner
  · intro axis
    rw [hpoint]
    exact norm_twoAxisStencilPoint_le_outer_add_four_of_support_pin
      (dyadicHodgeOuterCutoff (scale + 1)) first second haxes frequency
        firstPin secondPin (firstOrder + firstIndex) (secondOrder + secondIndex)
        hfirstStart hsecondStart hdistance hpinOuter axis

section Audit

#print axioms exists_directDyadicScalar_support_pin
#print axioms radius_sub_three_sq_le_frequencySquared_of_support_pin
#print axioms directDyadicScalar_support_controls_complementaryHodgeStencil

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeSupportStencil
