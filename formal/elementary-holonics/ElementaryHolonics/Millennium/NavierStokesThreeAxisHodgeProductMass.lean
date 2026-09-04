import ElementaryHolonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

/-!
# The twenty-seven Hodge product allocations and their full mixed mass

The three-axis `(2,2,2)` difference has sixty-four chronological binary Leibniz occurrences.
Commuting coordinate transport condenses them to twenty-seven allocation fibres indexed by the
number `0,1,2` of differences which meet the quadratic numerator on each axis.  This file keeps
the binomial occurrence multiplicity on every condensed face and derives the full mixed mass from
the reciprocal scale descent.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeScaleDescent

/-- The occurrence multiplicity for assigning zero, one, or two repeated differences to one
factor. -/
def secondOrderBinomialWeight : Fin 3 → ℕ := ![1, 2, 1]

/-- One of the twenty-seven commuting allocation faces, with the exact product-rule
multiplicity retained. -/
def threeAxisHodgeAllocationFace
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  ((secondOrderBinomialWeight firstAllocation *
      secondOrderBinomialWeight secondAllocation *
      secondOrderBinomialWeight thirdAllocation : ℕ) : ℂ) *
    threeAxisMixedForwardDifference 0 1 2
      firstAllocation.val secondAllocation.val thirdAllocation.val left frequency *
    threeAxisMixedForwardDifference 0 1 2
      (2 - firstAllocation.val) (2 - secondAllocation.val) (2 - thirdAllocation.val) right
      (threeAxisStencilPoint 0 1 2 frequency
        firstAllocation.val secondAllocation.val thirdAllocation.val)

/-- The same face before commuting the third-axis translation through the first two axes.  This
staged chart is the direct return of three successive second-order Leibniz expansions. -/
def stagedThreeAxisHodgeAllocationFace
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  ((secondOrderBinomialWeight firstAllocation *
      secondOrderBinomialWeight secondAllocation *
      secondOrderBinomialWeight thirdAllocation : ℕ) : ℂ) *
    mixedForwardDifference 0 1 firstAllocation.val secondAllocation.val
      ((fwdDiff (coordinateStep 2))^[thirdAllocation.val] left) frequency *
    mixedForwardDifference 0 1
      (2 - firstAllocation.val) (2 - secondAllocation.val)
      (fun current ↦
        (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
          (current + thirdAllocation.val • coordinateStep 2))
      (frequency + firstAllocation.val • coordinateStep 0 +
        secondAllocation.val • coordinateStep 1)

/-- Arbitrary iterated forward differences commute with an additive chart translation. -/
theorem fwdDiff_iter_translate_all
    (step offset : SpatialFrequency) (order : ℕ)
    (coefficient : SpatialFrequency → ℂ) :
    (fwdDiff step)^[order] (fun frequency ↦ coefficient (frequency + offset)) =
      fun frequency ↦ (fwdDiff step)^[order] coefficient (frequency + offset) := by
  induction order with
  | zero => rfl
  | succ order ih =>
      rw [Function.iterate_succ_apply', ih]
      simpa only [Function.iterate_succ_apply'] using
        fwdDiff_translate step offset ((fwdDiff step)^[order] coefficient)

/-- The two-axis mixed operator commutes with the same translated chart. -/
theorem mixedForwardDifference_translate_all
    (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (offset : SpatialFrequency) (coefficient : SpatialFrequency → ℂ) :
    mixedForwardDifference first second firstOrder secondOrder
        (fun frequency ↦ coefficient (frequency + offset)) =
      fun frequency ↦ mixedForwardDifference first second firstOrder secondOrder coefficient
        (frequency + offset) := by
  unfold mixedForwardDifference
  rw [fwdDiff_iter_translate_all, fwdDiff_iter_translate_all]

/-- Interchange of coordinate translations identifies the staged and simultaneous charts of
every allocation face. -/
theorem stagedThreeAxisHodgeAllocationFace_eq
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    stagedThreeAxisHodgeAllocationFace firstAllocation secondAllocation thirdAllocation
        left right frequency =
      threeAxisHodgeAllocationFace firstAllocation secondAllocation thirdAllocation
        left right frequency := by
  unfold stagedThreeAxisHodgeAllocationFace threeAxisHodgeAllocationFace
  rw [congrFun (mixedForwardDifference_translate_all 0 1
    (2 - firstAllocation.val) (2 - secondAllocation.val)
    (thirdAllocation.val • coordinateStep 2)
    ((fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right))
    (frequency + firstAllocation.val • coordinateStep 0 +
      secondAllocation.val • coordinateStep 1)]
  unfold threeAxisMixedForwardDifference mixedForwardDifference threeAxisStencilPoint
  congr 1

/-- The exact nine shifted first/second-axis Leibniz faces. -/
def twoAxisNineFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) : ℂ :=
  mixedForwardDifference first second 2 2 left frequency *
        right (frequency + coordinateStep second + coordinateStep second +
          coordinateStep first + coordinateStep first) +
    2 * mixedForwardDifference first second 1 2 left frequency *
        mixedForwardDifference first second 1 0 right
          (frequency + coordinateStep second + coordinateStep second + coordinateStep first) +
    mixedForwardDifference first second 0 2 left frequency *
        mixedForwardDifference first second 2 0 right
          (frequency + coordinateStep second + coordinateStep second) +
    2 * mixedForwardDifference first second 2 1 left frequency *
        mixedForwardDifference first second 0 1 right
          (frequency + coordinateStep first + coordinateStep first + coordinateStep second) +
    4 * mixedForwardDifference first second 1 1 left frequency *
        mixedForwardDifference first second 1 1 right
          (frequency + coordinateStep first + coordinateStep second) +
    2 * mixedForwardDifference first second 0 1 left frequency *
        mixedForwardDifference first second 2 1 right
          (frequency + coordinateStep second) +
    mixedForwardDifference first second 2 0 left frequency *
        mixedForwardDifference first second 0 2 right
          (frequency + coordinateStep first + coordinateStep first) +
    2 * mixedForwardDifference first second 1 0 left frequency *
        mixedForwardDifference first second 1 2 right
          (frequency + coordinateStep first) +
    left frequency * mixedForwardDifference first second 2 2 right frequency

theorem mixedForwardDifference_two_two_mul_eq_nineFaceReturn
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 2 2
        (fun current ↦ left current * right current) frequency =
      twoAxisNineFaceReturn first second left right frequency := by
  simpa [twoAxisNineFaceReturn] using
    mixedForwardDifference_two_two_mul_eq first second left right frequency

/-- The staged nine-face slice at one fixed third-axis allocation.  The outer coefficient is its
third-axis occurrence multiplicity; the enclosed return contains the remaining nine faces. -/
def stagedThreeAxisHodgeNineFaceReturn
    (thirdAllocation : Fin 3)
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  (secondOrderBinomialWeight thirdAllocation : ℂ) *
    twoAxisNineFaceReturn 0 1
      ((fwdDiff (coordinateStep 2))^[thirdAllocation.val] left)
      (fun current ↦
        (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
          (current + thirdAllocation.val • coordinateStep 2)) frequency

/-- The staged twenty-seven-face return before the final interchange comparison. -/
def stagedThreeAxisHodgeAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) : ℂ :=
  stagedThreeAxisHodgeNineFaceReturn 2 left right frequency +
    stagedThreeAxisHodgeNineFaceReturn 1 left right frequency +
      stagedThreeAxisHodgeNineFaceReturn 0 left right frequency

/-- The commuting twenty-seven-face receiver is the staged return, with every individual staged
face canonically identified with `threeAxisHodgeAllocationFace` above. -/
def threeAxisHodgeAllocationReturn := stagedThreeAxisHodgeAllocationReturn

/-- The ordinary two-axis nine-term identity, multiplied by the addressed third-axis occurrence
weight, is exactly one staged nine-face slice. -/
theorem secondOrderBinomialWeight_mul_mixedProduct_eq_stagedNineFaceReturn
    (thirdAllocation : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    (secondOrderBinomialWeight thirdAllocation : ℂ) *
        mixedForwardDifference 0 1 2 2
          (fun current ↦
            (fwdDiff (coordinateStep 2))^[thirdAllocation.val] left current *
              (fwdDiff (coordinateStep 2))^[2 - thirdAllocation.val] right
                (current + thirdAllocation.val • coordinateStep 2)) frequency =
      stagedThreeAxisHodgeNineFaceReturn thirdAllocation left right frequency := by
  unfold stagedThreeAxisHodgeNineFaceReturn
  rw [mixedForwardDifference_two_two_mul_eq_nineFaceReturn]

/-- Three consecutive second-order Leibniz expansions return exactly the staged twenty-seven
faces. -/
theorem threeAxisMixedForwardDifference_two_two_two_mul_eq_stagedAllocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 2 2 2
        (fun current ↦ left current * right current) frequency =
      stagedThreeAxisHodgeAllocationReturn left right frequency := by
  let thirdStep := coordinateStep 2
  let firstTerm : SpatialFrequency → ℂ := fun current ↦
    (fwdDiff thirdStep)^[2] left current *
      right (current + thirdStep + thirdStep)
  let middleTerm : SpatialFrequency → ℂ := fun current ↦
    fwdDiff thirdStep left current * fwdDiff thirdStep right (current + thirdStep)
  let lastTerm : SpatialFrequency → ℂ := fun current ↦
    left current * (fwdDiff thirdStep)^[2] right current
  have hthirdProduct :
      (fwdDiff thirdStep)^[2] (fun current ↦ left current * right current) =
        firstTerm + (2 : ℂ) • middleTerm + lastTerm := by
    funext current
    simpa [firstTerm, middleTerm, lastTerm, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_assoc] using
        fwdDiff_iter_two_mul_eq thirdStep left right current
  unfold threeAxisMixedForwardDifference
  rw [hthirdProduct, fwdDiff_iter_add, fwdDiff_iter_add,
    fwdDiff_iter_add, fwdDiff_iter_const_smul, fwdDiff_iter_add,
    fwdDiff_iter_const_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change
    mixedForwardDifference 0 1 2 2 firstTerm frequency +
        2 * mixedForwardDifference 0 1 2 2 middleTerm frequency +
      mixedForwardDifference 0 1 2 2 lastTerm frequency = _
  have htwo := secondOrderBinomialWeight_mul_mixedProduct_eq_stagedNineFaceReturn
    (2 : Fin 3) left right frequency
  have hone := secondOrderBinomialWeight_mul_mixedProduct_eq_stagedNineFaceReturn
    (1 : Fin 3) left right frequency
  have hzero := secondOrderBinomialWeight_mul_mixedProduct_eq_stagedNineFaceReturn
    (0 : Fin 3) left right frequency
  unfold stagedThreeAxisHodgeAllocationReturn
  have htwo' : mixedForwardDifference 0 1 2 2 firstTerm frequency =
      stagedThreeAxisHodgeNineFaceReturn 2 left right frequency := by
    simp [secondOrderBinomialWeight, firstTerm, thirdStep,
      Function.iterate_zero_apply] at htwo ⊢
    convert htwo using 1
    apply congrArg (fun coefficient : SpatialFrequency → ℂ ↦
      mixedForwardDifference 0 1 2 2 coefficient frequency)
    funext current
    congr 2
    funext other
    simp
    ring
  have hone' : 2 * mixedForwardDifference 0 1 2 2 middleTerm frequency =
      stagedThreeAxisHodgeNineFaceReturn 1 left right frequency := by
    simpa [secondOrderBinomialWeight, middleTerm, thirdStep,
      Function.iterate_zero_apply, Function.iterate_one] using hone
  have hzero' : mixedForwardDifference 0 1 2 2 lastTerm frequency =
      stagedThreeAxisHodgeNineFaceReturn 0 left right frequency := by
    simpa [secondOrderBinomialWeight, lastTerm, thirdStep,
      Function.iterate_zero_apply, Function.iterate_one] using hzero
  rw [htwo', hone', hzero']

/-- Exact three-axis shifted Leibniz law after the commuting allocation quotient. -/
theorem threeAxisMixedForwardDifference_two_two_two_mul_eq_allocationReturn
    (left right : SpatialFrequency → ℂ) (frequency : SpatialFrequency) :
    threeAxisMixedForwardDifference 0 1 2 2 2 2
        (fun current ↦ left current * right current) frequency =
      threeAxisHodgeAllocationReturn left right frequency := by
  simpa [threeAxisHodgeAllocationReturn] using
    threeAxisMixedForwardDifference_two_two_two_mul_eq_stagedAllocationReturn
      left right frequency

/-- The returned face family really has `3^3 = 27` allocation addresses. -/
theorem threeAxisHodgeAllocation_face_card :
    Fintype.card ThreeAxisSecondOrderAllocation = 27 :=
  threeAxisSecondOrderAllocation_card

/-! ## Quadratic numerator annihilation -/

/-- Any three addressed coordinate differences annihilate the quadratic Hodge numerator, whether
or not the axes repeat. -/
@[simp] theorem hodgeJacobianRatioNumerator_threeDifferences_eq_zero
    (first second third : Fin 3) (component coordinate input : Fin 3) :
    fwdDiff (coordinateStep first)
      (fwdDiff (coordinateStep second)
        (fwdDiff (coordinateStep third)
          (fun current ↦ hodgeJacobianRatioNumerator current
            component coordinate input))) = 0 := by
  rw [show (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input) =
      (-1 : ℂ) • (fun current ↦ (current coordinate : ℂ) *
        hodgeCrossBasisFactor current component input) by
    funext current
    simp [hodgeJacobianRatioNumerator]]
  rw [fwdDiff_const_smul, fwdDiff_const_smul, fwdDiff_const_smul]
  have hproduct := fwdDiff_fwdDiff_mul_of_linear
    (coordinateStep second) (coordinateStep third)
    (fun current : SpatialFrequency ↦ (current coordinate : ℂ))
    (fun current ↦ hodgeCrossBasisFactor current component input)
    (if second = coordinate then 1 else 0)
    (if third = coordinate then 1 else 0)
    (hodgeCrossBasisFactor (coordinateStep second) component input)
    (hodgeCrossBasisFactor (coordinateStep third) component input)
    (fwdDiff_coordinate_eq second coordinate)
    (fwdDiff_coordinate_eq third coordinate)
    (fwdDiff_hodgeCrossBasisFactor_eq second component input)
    (fwdDiff_hodgeCrossBasisFactor_eq third component input)
  rw [hproduct]
  funext current
  simp

@[simp] theorem fwdDiff_zero_section (step : SpatialFrequency) :
    fwdDiff step (0 : SpatialFrequency → ℂ) = 0 := by
  funext current
  simp [fwdDiff]

/-- Every allocation which sends total order at least three to the quadratic numerator vanishes. -/
theorem hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
    (firstAllocation secondAllocation thirdAllocation : Fin 3)
    (component coordinate input : Fin 3)
    (horder : 3 ≤ firstAllocation.val + secondAllocation.val + thirdAllocation.val) :
    threeAxisMixedForwardDifference 0 1 2
      firstAllocation.val secondAllocation.val thirdAllocation.val
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input) = 0 := by
  fin_cases firstAllocation <;> fin_cases secondAllocation <;>
    fin_cases thirdAllocation <;>
    simp_all [threeAxisMixedForwardDifference, Function.iterate_succ_apply']

/-! ## The ten surviving allocation classes -/

/-- The contribution of the third-axis-zero slice after quadratic annihilation. -/
def hodgeFullMixedThirdZeroEnvelope (lower bound : ℝ) : ℝ :=
  3 * bound ^ 2 * hodgeReciprocal222Envelope lower bound +
    4 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound +
      4 * hodgeReciprocalMixedTwoTwoEnvelope lower bound +
        8 * hodgeReciprocal112Envelope lower bound

/-- The third-axis-zero slice retains six of its nine allocations. -/
theorem norm_hodgeFullMixedThirdZeroSlice_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 2) :
    ‖stagedThreeAxisHodgeNineFaceReturn 0
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
      hodgeReciprocal frequency‖ ≤ hodgeFullMixedThirdZeroEnvelope lower bound := by
  let numerator := fun current ↦
    hodgeJacobianRatioNumerator current component coordinate input
  let reciprocal := hodgeReciprocal
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).2
  have hn00 : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hn10 : ‖mixedForwardDifference 0 1 1 0 numerator frequency‖ ≤ 2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
      hbound 0 1 frequency hcoordinates component coordinate input
  have hn01 : ‖mixedForwardDifference 0 1 0 1 numerator frequency‖ ≤ 2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
      hbound 0 1 frequency hcoordinates component coordinate input
  have hn20 : ‖mixedForwardDifference 0 1 2 0 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_two_zero_le_two
      0 1 frequency component coordinate input
  have hn02 : ‖mixedForwardDifference 0 1 0 2 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_two_le_two
      0 1 frequency component coordinate input
  have hn11 : ‖mixedForwardDifference 0 1 1 1 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
      0 1 frequency component coordinate input
  have hn12 : mixedForwardDifference 0 1 1 2 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
      0 1 frequency component coordinate input
  have hn21 : mixedForwardDifference 0 1 2 1 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_two_one_eq_zero
      0 1 frequency component coordinate input
  have hn22 : mixedForwardDifference 0 1 2 2 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_two_two_eq_zero
      0 1 frequency component coordinate input
  have hr222 : ‖mixedForwardDifference 0 1 2 2
      ((fwdDiff (coordinateStep 2))^[2] reciprocal) frequency‖ ≤
      hodgeReciprocal222Envelope lower bound := by
    have hraw := norm_hodgeReciprocal_secondEachAxis_le_of_controlled
      hlower hbound frequency hstencil
    rw [show secondEachAxisWord =
      List.replicate 2 0 ++ List.replicate 2 1 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference] using hraw
  have hr122First : ‖mixedForwardDifference 0 1 1 2
      ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0)‖ ≤ hodgeReciprocal122Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 1) (secondOffset := 0) (thirdOffset := 0)
      (firstOrder := 1) (secondOrder := 2) (thirdOrder := 2)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneTwoTwoWord 0)
        (threeAxisStencilPoint 0 1 2 frequency 1 0 0),
        frequencySquared current ≠ 0 := by
      simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
      hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 1 0 0) hsub hnonzero
    rw [show oneTwoTwoWord 0 =
      List.replicate 1 0 ++ List.replicate 2 1 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  have hr122Second : ‖mixedForwardDifference 0 1 2 1
      ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 1)‖ ≤ hodgeReciprocal122Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 0) (secondOffset := 1) (thirdOffset := 0)
      (firstOrder := 2) (secondOrder := 1) (thirdOrder := 2)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneTwoTwoWord 1)
        (threeAxisStencilPoint 0 1 2 frequency 0 1 0),
        frequencySquared current ≠ 0 := by
      simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
      hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 0 1 0) hsub hnonzero
    rw [show oneTwoTwoWord 1 =
      List.replicate 2 0 ++ List.replicate 1 1 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  have hr22First : ‖mixedForwardDifference 0 1 0 2
      ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0 + coordinateStep 0)‖ ≤
      hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_pairWord_two_two_le
      hlower hbound 1 2 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 2 0 0)
      (hstencil.secondThird (firstOffset := 2) (by omega))
    rw [show ([1, 1, 2, 2] : List (Fin 3)) =
        List.replicate 2 1 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_mixedForwardDifference] at hraw
    have hbase : threeAxisStencilPoint 0 1 2 frequency 2 0 0 =
        frequency + coordinateStep 0 + coordinateStep 0 := by
      funext other
      simp [threeAxisStencilPoint]
      ring
    rw [hbase] at hraw
    simpa [mixedForwardDifference] using hraw
  have hr22Second : ‖mixedForwardDifference 0 1 2 0
      ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 1 + coordinateStep 1)‖ ≤
      hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_pairWord_two_two_le
      hlower hbound 0 2 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 0 2 0)
      (hstencil.firstThird (secondOffset := 2) (by omega))
    rw [show ([0, 0, 2, 2] : List (Fin 3)) =
        List.replicate 2 0 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_mixedForwardDifference] at hraw
    have hbase : threeAxisStencilPoint 0 1 2 frequency 0 2 0 =
        frequency + coordinateStep 1 + coordinateStep 1 := by
      funext other
      simp [threeAxisStencilPoint]
      ring
    rw [hbase] at hraw
    simpa [mixedForwardDifference] using hraw
  have hr112 : ‖mixedForwardDifference 0 1 1 1
      ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0 + coordinateStep 1)‖ ≤
      hodgeReciprocal112Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 1) (secondOffset := 1) (thirdOffset := 0)
      (firstOrder := 1) (secondOrder := 1) (thirdOrder := 2)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneOneTwoWord 2)
        (threeAxisStencilPoint 0 1 2 frequency 1 1 0),
        frequencySquared current ≠ 0 := by
      simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
      hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 1 1 0) hsub hnonzero
    rw [show oneOneTwoWord 2 =
      List.replicate 1 0 ++ List.replicate 1 1 ++ List.replicate 2 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  let a := mixedForwardDifference 0 1 2 2 numerator frequency *
    (fwdDiff (coordinateStep 2))^[2] reciprocal
      (frequency + coordinateStep 1 + coordinateStep 1 +
        coordinateStep 0 + coordinateStep 0)
  let b := 2 * mixedForwardDifference 0 1 1 2 numerator frequency *
    mixedForwardDifference 0 1 1 0 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 1 + coordinateStep 1 + coordinateStep 0)
  let c := mixedForwardDifference 0 1 0 2 numerator frequency *
    mixedForwardDifference 0 1 2 0 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 1 + coordinateStep 1)
  let d := 2 * mixedForwardDifference 0 1 2 1 numerator frequency *
    mixedForwardDifference 0 1 0 1 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0 + coordinateStep 0 + coordinateStep 1)
  let e := 4 * mixedForwardDifference 0 1 1 1 numerator frequency *
    mixedForwardDifference 0 1 1 1 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0 + coordinateStep 1)
  let f := 2 * mixedForwardDifference 0 1 0 1 numerator frequency *
    mixedForwardDifference 0 1 2 1 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 1)
  let g := mixedForwardDifference 0 1 2 0 numerator frequency *
    mixedForwardDifference 0 1 0 2 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0 + coordinateStep 0)
  let h := 2 * mixedForwardDifference 0 1 1 0 numerator frequency *
    mixedForwardDifference 0 1 1 2 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
      (frequency + coordinateStep 0)
  let i := numerator frequency *
    mixedForwardDifference 0 1 2 2 ((fwdDiff (coordinateStep 2))^[2] reciprocal) frequency
  have ha : ‖a‖ ≤ 0 := by simp [a, hn22]
  have hb : ‖b‖ ≤ 0 := by simp [b, hn12]
  have hc : ‖c‖ ≤ 2 * hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    dsimp [c]
    rw [norm_mul]
    exact mul_le_mul hn02 hr22Second (norm_nonneg _) (by positivity)
  have hd : ‖d‖ ≤ 0 := by simp [d, hn21]
  have he : ‖e‖ ≤ 8 * hodgeReciprocal112Envelope lower bound := by
    dsimp [e]
    simp only [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hp := mul_le_mul hn11 hr112 (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
    calc
      4 * ‖mixedForwardDifference 0 1 1 1 numerator frequency‖ *
          ‖mixedForwardDifference 0 1 1 1 ((fwdDiff (coordinateStep 2))^[2] reciprocal)
            (frequency + coordinateStep 0 + coordinateStep 1)‖ ≤
          4 * (2 * hodgeReciprocal112Envelope lower bound) :=
        by simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 by norm_num)
      _ = 8 * hodgeReciprocal112Envelope lower bound := by ring
  have hf : ‖f‖ ≤ 2 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound := by
    dsimp [f]
    simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hp := mul_le_mul hn01 hr122Second (norm_nonneg _)
      (by positivity : 0 ≤ 2 * bound + 1)
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)
  have hg : ‖g‖ ≤ 2 * hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    dsimp [g]
    rw [norm_mul]
    exact mul_le_mul hn20 hr22First (norm_nonneg _) (by positivity)
  have hh : ‖h‖ ≤ 2 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound := by
    dsimp [h]
    simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hp := mul_le_mul hn10 hr122First (norm_nonneg _)
      (by positivity : 0 ≤ 2 * bound + 1)
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)
  have hi : ‖i‖ ≤ 3 * bound ^ 2 * hodgeReciprocal222Envelope lower bound := by
    dsimp [i]
    rw [norm_mul]
    exact mul_le_mul hn00 hr222 (norm_nonneg _) (by positivity)
  unfold stagedThreeAxisHodgeNineFaceReturn
  simp [secondOrderBinomialWeight, Function.iterate_zero_apply]
  unfold twoAxisNineFaceReturn
  change ‖a + b + c + d + e + f + g + h + i‖ ≤ _
  rw [show a + b + c + d + e + f + g + h + i =
    a + (b + (c + (d + (e + (f + (g + (h + i))))))) by ring]
  refine (norm_add_nine_le a b c d e f g h i).trans ?_
  unfold hodgeFullMixedThirdZeroEnvelope
  linarith

/-- The contribution of the third-axis-one slice after quadratic annihilation. -/
def hodgeFullMixedThirdOneEnvelope (lower bound : ℝ) : ℝ :=
  2 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound +
    16 * hodgeReciprocal112Envelope lower bound

/-- The third-axis-one slice retains exactly three of its nine allocations. -/
theorem norm_hodgeFullMixedThirdOneSlice_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 2) :
    ‖stagedThreeAxisHodgeNineFaceReturn 1
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
      hodgeReciprocal frequency‖ ≤ hodgeFullMixedThirdOneEnvelope lower bound := by
  let numerator := fun current ↦
    hodgeJacobianRatioNumerator current component coordinate input
  let reciprocal := hodgeReciprocal
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa using (hstencil 0 (by omega) 0 (by omega) 0 (by omega)).2
  have hn00 : ‖fwdDiff (coordinateStep 2) numerator frequency‖ ≤ 2 * bound + 1 := by
    simpa [mixedForwardDifference, Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
        hbound 2 0 frequency hcoordinates component coordinate input
  have hn10 : ‖mixedForwardDifference 0 1 1 0
      (fwdDiff (coordinateStep 2) numerator) frequency‖ ≤ 2 := by
    simpa [mixedForwardDifference, Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
        0 2 frequency component coordinate input
  have hn01 : ‖mixedForwardDifference 0 1 0 1
      (fwdDiff (coordinateStep 2) numerator) frequency‖ ≤ 2 := by
    simpa [mixedForwardDifference, Function.iterate_one] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
        1 2 frequency component coordinate input
  have hnzero : ∀ firstAllocation secondAllocation : Fin 3,
      3 ≤ firstAllocation.val + secondAllocation.val + 1 →
      mixedForwardDifference 0 1 firstAllocation.val secondAllocation.val
        (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    intro firstAllocation secondAllocation horder
    have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        firstAllocation secondAllocation 1 component coordinate input horder) frequency
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      Function.iterate_one] using hzero
  have hr122 : ‖mixedForwardDifference 0 1 2 2
      (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
        (current + coordinateStep 2)) frequency‖ ≤
      hodgeReciprocal122Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 0) (secondOffset := 0) (thirdOffset := 1)
      (firstOrder := 2) (secondOrder := 2) (thirdOrder := 1)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneTwoTwoWord 2)
        (threeAxisStencilPoint 0 1 2 frequency 0 0 1),
        frequencySquared current ≠ 0 := by
      simpa [oneTwoTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneTwoTwo_le_of_controlled
      hlower hbound 2 (threeAxisStencilPoint 0 1 2 frequency 0 0 1) hsub hnonzero
    rw [show oneTwoTwoWord 2 =
      List.replicate 2 0 ++ List.replicate 2 1 ++ List.replicate 1 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    have htranslated := congrFun (mixedForwardDifference_translate_all 0 1 2 2
      (coordinateStep 2) (fwdDiff (coordinateStep 2) reciprocal)) frequency
    rw [htranslated]
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  have hr112First : ‖mixedForwardDifference 0 1 1 2
      (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
        (current + coordinateStep 2)) (frequency + coordinateStep 0)‖ ≤
      hodgeReciprocal112Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 1) (secondOffset := 0) (thirdOffset := 1)
      (firstOrder := 1) (secondOrder := 2) (thirdOrder := 1)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneOneTwoWord 1)
        (threeAxisStencilPoint 0 1 2 frequency 1 0 1),
        frequencySquared current ≠ 0 := by
      simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
      hlower hbound 1 (threeAxisStencilPoint 0 1 2 frequency 1 0 1) hsub hnonzero
    rw [show oneOneTwoWord 1 =
      List.replicate 1 0 ++ List.replicate 2 1 ++ List.replicate 1 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    have htranslated := congrFun (mixedForwardDifference_translate_all 0 1 1 2
      (coordinateStep 2) (fwdDiff (coordinateStep 2) reciprocal))
      (frequency + coordinateStep 0)
    rw [htranslated]
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  have hr112Second : ‖mixedForwardDifference 0 1 2 1
      (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
        (current + coordinateStep 2)) (frequency + coordinateStep 1)‖ ≤
      hodgeReciprocal112Envelope lower bound := by
    have hsub := hstencil.rebase
      (firstOffset := 0) (secondOffset := 1) (thirdOffset := 1)
      (firstOrder := 2) (secondOrder := 1) (thirdOrder := 1)
      (by omega) (by omega) (by omega)
    have hnonzero : ∀ current ∈ successorWindow coordinateTransport (oneOneTwoWord 0)
        (threeAxisStencilPoint 0 1 2 frequency 0 1 1),
        frequencySquared current ≠ 0 := by
      simpa [oneOneTwoWord] using hsub.successor_nonzero hlower
    have hraw := norm_hodgeReciprocal_oneOneTwo_le_of_controlled
      hlower hbound 0 (threeAxisStencilPoint 0 1 2 frequency 0 1 1) hsub hnonzero
    rw [show oneOneTwoWord 0 =
      List.replicate 2 0 ++ List.replicate 1 1 ++ List.replicate 1 2 by rfl,
      differenceWord_eq_threeAxisMixedForwardDifference] at hraw
    have htranslated := congrFun (mixedForwardDifference_translate_all 0 1 2 1
      (coordinateStep 2) (fwdDiff (coordinateStep 2) reciprocal))
      (frequency + coordinateStep 1)
    rw [htranslated]
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference,
      threeAxisStencilPoint] using hraw
  let f := 4 * mixedForwardDifference 0 1 0 1
    (fwdDiff (coordinateStep 2) numerator) frequency *
      mixedForwardDifference 0 1 2 1
        (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
          (current + coordinateStep 2)) (frequency + coordinateStep 1)
  let h := 4 * mixedForwardDifference 0 1 1 0
    (fwdDiff (coordinateStep 2) numerator) frequency *
      mixedForwardDifference 0 1 1 2
        (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
          (current + coordinateStep 2)) (frequency + coordinateStep 0)
  let i := 2 * fwdDiff (coordinateStep 2) numerator frequency *
    mixedForwardDifference 0 1 2 2
      (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
        (current + coordinateStep 2)) frequency
  have hf : ‖f‖ ≤ 8 * hodgeReciprocal112Envelope lower bound := by
    dsimp [f]
    simp only [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hp := mul_le_mul hn01 hr112Second (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
    calc
      4 * ‖mixedForwardDifference 0 1 0 1 (fwdDiff (coordinateStep 2) numerator) frequency‖ *
          ‖mixedForwardDifference 0 1 2 1
            (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
              (current + coordinateStep 2)) (frequency + coordinateStep 1)‖ =
          4 * (‖mixedForwardDifference 0 1 0 1
              (fwdDiff (coordinateStep 2) numerator) frequency‖ *
            ‖mixedForwardDifference 0 1 2 1
              (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
                (current + coordinateStep 2)) (frequency + coordinateStep 1)‖) := by ring
      _ ≤ 4 * (2 * hodgeReciprocal112Envelope lower bound) :=
        mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 by norm_num)
      _ = 8 * hodgeReciprocal112Envelope lower bound := by ring
  have hh : ‖h‖ ≤ 8 * hodgeReciprocal112Envelope lower bound := by
    dsimp [h]
    simp only [norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hp := mul_le_mul hn10 hr112First (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
    calc
      4 * ‖mixedForwardDifference 0 1 1 0 (fwdDiff (coordinateStep 2) numerator) frequency‖ *
          ‖mixedForwardDifference 0 1 1 2
            (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
              (current + coordinateStep 2)) (frequency + coordinateStep 0)‖ =
          4 * (‖mixedForwardDifference 0 1 1 0
              (fwdDiff (coordinateStep 2) numerator) frequency‖ *
            ‖mixedForwardDifference 0 1 1 2
              (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
                (current + coordinateStep 2)) (frequency + coordinateStep 0)‖) := by ring
      _ ≤ 4 * (2 * hodgeReciprocal112Envelope lower bound) :=
        mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 4 by norm_num)
      _ = 8 * hodgeReciprocal112Envelope lower bound := by ring
  have hi : ‖i‖ ≤ 2 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound := by
    dsimp [i]
    simp only [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hp := mul_le_mul hn00 hr122 (norm_nonneg _) (by positivity : 0 ≤ 2 * bound + 1)
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 2 by norm_num)
  have hn02 : mixedForwardDifference 0 1 0 2
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 0 2 (by norm_num)
  have hn11 : mixedForwardDifference 0 1 1 1
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 1 1 (by norm_num)
  have hn20 : mixedForwardDifference 0 1 2 0
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 2 0 (by norm_num)
  have hn12 : mixedForwardDifference 0 1 1 2
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 1 2 (by norm_num)
  have hn21 : mixedForwardDifference 0 1 2 1
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 2 1 (by norm_num)
  have hn22 : mixedForwardDifference 0 1 2 2
      (fwdDiff (coordinateStep 2) numerator) frequency = 0 := by
    simpa using hnzero 2 2 (by norm_num)
  have hreturn : stagedThreeAxisHodgeNineFaceReturn 1 numerator reciprocal frequency =
      f + h + i := by
    unfold stagedThreeAxisHodgeNineFaceReturn
    change 2 * twoAxisNineFaceReturn 0 1 (fwdDiff (coordinateStep 2) numerator)
      (fun current ↦ fwdDiff (coordinateStep 2) reciprocal
        (current + coordinateStep 2)) frequency = f + h + i
    unfold twoAxisNineFaceReturn
    rw [hn22, hn12, hn02, hn21, hn11, hn20]
    simp [f, h, i]
    ring
  rw [show (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input) =
      numerator by rfl, show hodgeReciprocal = reciprocal by rfl, hreturn]
  calc
    ‖f + h + i‖ ≤ ‖f + h‖ + ‖i‖ := norm_add_le _ _
    _ ≤ (‖f‖ + ‖h‖) + ‖i‖ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ hodgeFullMixedThirdOneEnvelope lower bound := by
      unfold hodgeFullMixedThirdOneEnvelope
      linarith

/-- The contribution of the third-axis-two slice after quadratic annihilation. -/
def hodgeFullMixedThirdTwoEnvelope (lower bound : ℝ) : ℝ :=
  2 * hodgeReciprocalMixedTwoTwoEnvelope lower bound

/-- The third-axis-two slice retains only the allocation which sends no first- or second-axis
difference to the already quadratic-order-two numerator. -/
theorem norm_hodgeFullMixedThirdTwoSlice_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 2) :
    ‖stagedThreeAxisHodgeNineFaceReturn 2
      (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input)
      hodgeReciprocal frequency‖ ≤ hodgeFullMixedThirdTwoEnvelope lower bound := by
  let numerator := fun current ↦
    hodgeJacobianRatioNumerator current component coordinate input
  let reciprocal := hodgeReciprocal
  have hn00 : ‖(fwdDiff (coordinateStep 2))^[2] numerator frequency‖ ≤ 2 := by
    simpa [mixedForwardDifference] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_two_zero_le_two
        2 0 frequency component coordinate input
  have hnzero : ∀ firstAllocation secondAllocation : Fin 3,
      1 ≤ firstAllocation.val + secondAllocation.val →
      mixedForwardDifference 0 1 firstAllocation.val secondAllocation.val
        ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    intro firstAllocation secondAllocation horder
    have hzero := congrFun
      (hodgeJacobianRatioNumerator_allocation_eq_zero_of_three_le
        firstAllocation secondAllocation 2 component coordinate input (by omega)) frequency
    simpa [threeAxisMixedForwardDifference, mixedForwardDifference] using hzero
  have hr22 : ‖mixedForwardDifference 0 1 2 2
      (fun current ↦ reciprocal (current + 2 • coordinateStep 2)) frequency‖ ≤
      hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    have hraw := norm_hodgeReciprocal_pairWord_two_two_le
      hlower hbound 0 1 (by decide)
      (threeAxisStencilPoint 0 1 2 frequency 0 0 2)
      (hstencil.firstSecond (thirdOffset := 2) (by omega))
    rw [show ([0, 0, 1, 1] : List (Fin 3)) =
        List.replicate 2 0 ++ List.replicate 2 1 by rfl,
      differenceWord_eq_mixedForwardDifference] at hraw
    have htranslated := congrFun (mixedForwardDifference_translate_all 0 1 2 2
      (2 • coordinateStep 2) reciprocal) frequency
    rw [htranslated]
    simpa [threeAxisStencilPoint] using hraw
  have hn01 : mixedForwardDifference 0 1 0 1
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 0 1 (by norm_num)
  have hn02 : mixedForwardDifference 0 1 0 2
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 0 2 (by norm_num)
  have hn10 : mixedForwardDifference 0 1 1 0
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 1 0 (by norm_num)
  have hn11 : mixedForwardDifference 0 1 1 1
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 1 1 (by norm_num)
  have hn12 : mixedForwardDifference 0 1 1 2
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 1 2 (by norm_num)
  have hn20 : mixedForwardDifference 0 1 2 0
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 2 0 (by norm_num)
  have hn21 : mixedForwardDifference 0 1 2 1
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 2 1 (by norm_num)
  have hn22 : mixedForwardDifference 0 1 2 2
      ((fwdDiff (coordinateStep 2))^[2] numerator) frequency = 0 := by
    simpa using hnzero 2 2 (by norm_num)
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
    at hn01 hn02 hn10 hn11 hn12 hn20 hn21 hn22
  let i := (fwdDiff (coordinateStep 2))^[2] numerator frequency *
    mixedForwardDifference 0 1 2 2
      (fun current ↦ reciprocal (current + 2 • coordinateStep 2)) frequency
  have hi : ‖i‖ ≤ hodgeFullMixedThirdTwoEnvelope lower bound := by
    dsimp [i, hodgeFullMixedThirdTwoEnvelope]
    rw [norm_mul]
    exact mul_le_mul hn00 hr22 (norm_nonneg _) (by positivity)
  have hreturn : stagedThreeAxisHodgeNineFaceReturn 2 numerator reciprocal frequency = i := by
    unfold stagedThreeAxisHodgeNineFaceReturn
    simp [secondOrderBinomialWeight, Function.iterate_zero_apply]
    unfold twoAxisNineFaceReturn
    rw [hn22, hn12, hn02, hn21, hn11, hn01, hn20, hn10]
    simp [i, Function.iterate_succ_apply']
  rw [show (fun current ↦ hodgeJacobianRatioNumerator current component coordinate input) =
      numerator by rfl, show hodgeReciprocal = reciprocal by rfl, hreturn]
  exact hi

/-! ## The full mixed Hodge mass -/

/-- The exact envelope returned by the ten surviving `(2,2,2)` Hodge allocations.  Every
reciprocal term has already descended to strictly lower order in the scale ledger. -/
def hodgeJacobianEntryThreeAxisFullMixedEnvelope (lower bound : ℝ) : ℝ :=
  3 * bound ^ 2 * hodgeReciprocal222Envelope lower bound +
    6 * (2 * bound + 1) * hodgeReciprocal122Envelope lower bound +
      6 * hodgeReciprocalMixedTwoTwoEnvelope lower bound +
        24 * hodgeReciprocal112Envelope lower bound

/-- The actual Hodge multiplier entry has a derived three-axis full mixed mass.  The hypotheses
control one addressed `3 × 3 × 3` successor window; no independent allocation-face bound is
assumed. -/
theorem norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_two_two_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : ThreeAxisStencilControlled lower bound 0 1 2 frequency 2 2 2) :
    ‖threeAxisMixedForwardDifference 0 1 2 2 2 2
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input)
      frequency‖ ≤ hodgeJacobianEntryThreeAxisFullMixedEnvelope lower bound := by
  let numerator := fun current ↦
    hodgeJacobianRatioNumerator current component coordinate input
  let reciprocal := hodgeReciprocal
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeJacobianRatioNumerator, hodgeReciprocal,
      hodgeCrossBasisFactor, div_eq_mul_inv]
  have htwo := norm_hodgeFullMixedThirdTwoSlice_le hlower hbound
    frequency component coordinate input hstencil
  have hone := norm_hodgeFullMixedThirdOneSlice_le hlower hbound
    frequency component coordinate input hstencil
  have hzero := norm_hodgeFullMixedThirdZeroSlice_le hlower hbound
    frequency component coordinate input hstencil
  rw [hentry,
    threeAxisMixedForwardDifference_two_two_two_mul_eq_allocationReturn]
  unfold threeAxisHodgeAllocationReturn stagedThreeAxisHodgeAllocationReturn
  calc
    ‖stagedThreeAxisHodgeNineFaceReturn 2 numerator reciprocal frequency +
        stagedThreeAxisHodgeNineFaceReturn 1 numerator reciprocal frequency +
          stagedThreeAxisHodgeNineFaceReturn 0 numerator reciprocal frequency‖ ≤
        (‖stagedThreeAxisHodgeNineFaceReturn 2 numerator reciprocal frequency‖ +
          ‖stagedThreeAxisHodgeNineFaceReturn 1 numerator reciprocal frequency‖) +
            ‖stagedThreeAxisHodgeNineFaceReturn 0 numerator reciprocal frequency‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ hodgeFullMixedThirdTwoEnvelope lower bound +
          hodgeFullMixedThirdOneEnvelope lower bound +
            hodgeFullMixedThirdZeroEnvelope lower bound := by
      exact add_le_add (add_le_add htwo hone) hzero
    _ = hodgeJacobianEntryThreeAxisFullMixedEnvelope lower bound := by
      unfold hodgeFullMixedThirdTwoEnvelope hodgeFullMixedThirdOneEnvelope
        hodgeFullMixedThirdZeroEnvelope hodgeJacobianEntryThreeAxisFullMixedEnvelope
      ring

end Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass

section Audit
open Soma.Holonics.Millennium.NavierStokesThreeAxisHodgeProductMass
#print axioms threeAxisMixedForwardDifference_two_two_two_mul_eq_allocationReturn
#print axioms threeAxisHodgeAllocation_face_card
#print axioms hodgeJacobianRatioNumerator_threeDifferences_eq_zero
#print axioms norm_hodgeJacobianMultiplierEntry_threeAxisMixedForwardDifference_two_two_two_le
end Audit
