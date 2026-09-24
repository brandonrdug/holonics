import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeMixedVariation
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Higher mixed variation of the actual annular Hodge coefficient

**[proved-derived]** This owner develops the order-four discrete rational calculus required by
the two-coordinate annular Hodge mass.  Coordinate steps remain genuine integer-frequency
translations.  Numerator cancellation, reciprocal transport, and aperture residues are retained
separately; no physical-kernel or mixed-mass conclusion is accepted as a premise.
-/

noncomputable section

open scoped BigOperators fwdDiff

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularTensorCoefficientVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeStencilSum
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeInnerStencilSum
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedFubini
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeMixedVariation

/-! ## Genuine coordinate steps and commuting finite differences -/

/-- Unit translation in one genuine lattice coordinate. -/
def coordinateStep (axis : Fin 3) : SpatialFrequency := Pi.single axis 1

/-- Adding the unit lattice step is the existing addressed coordinate increment. -/
theorem add_coordinateStep_eq_increment (axis : Fin 3) (frequency : SpatialFrequency) :
    frequency + coordinateStep axis = incrementFrequencyCoordinate axis frequency := by
  funext other
  fin_cases axis <;> fin_cases other <;>
    simp [coordinateStep, incrementFrequencyCoordinate, replaceFrequencyCoordinate]

/-- Iterated forward differences in two addressed lattice coordinates. -/
def mixedForwardDifference
    (first second : Fin 3) (firstOrder secondOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) : SpatialFrequency → ℂ :=
  (fwdDiff (coordinateStep first))^[firstOrder]
    ((fwdDiff (coordinateStep second))^[secondOrder] coefficient)

/-- A coordinate projection changes by its Kronecker value under a unit lattice step. -/
theorem fwdDiff_coordinate_eq (axis coordinate : Fin 3) :
    fwdDiff (coordinateStep axis)
      (fun frequency : SpatialFrequency ↦ (frequency coordinate : ℂ)) =
      fun _ ↦ if axis = coordinate then 1 else 0 := by
  fin_cases axis <;> fin_cases coordinate <;>
    funext frequency <;> simp [fwdDiff, coordinateStep]

/-- The cross-basis factor is additive in its frequency argument. -/
theorem hodgeCrossBasisFactor_add
    (first second : SpatialFrequency) (component input : Fin 3) :
    hodgeCrossBasisFactor (first + second) component input =
      hodgeCrossBasisFactor first component input +
        hodgeCrossBasisFactor second component input := by
  fin_cases component <;> fin_cases input <;>
    simp [hodgeCrossBasisFactor, complexCross, complexFrequencyVector,
      crossProduct] <;> ring

/-- The first difference of the cross-basis factor is the same factor evaluated on the step. -/
theorem fwdDiff_hodgeCrossBasisFactor_eq (axis component input : Fin 3) :
    fwdDiff (coordinateStep axis)
      (fun frequency : SpatialFrequency ↦
        hodgeCrossBasisFactor frequency component input) =
      fun _ ↦ hodgeCrossBasisFactor (coordinateStep axis) component input := by
  funext frequency
  rw [fwdDiff, hodgeCrossBasisFactor_add]
  ring

/-- Second finite difference of a product of two affine lattice readings. -/
theorem fwdDiff_iter_two_mul_of_linear
    (step : SpatialFrequency) (first second : SpatialFrequency → ℂ)
    (firstChange secondChange : ℂ)
    (hfirst : fwdDiff step first = fun _ ↦ firstChange)
    (hsecond : fwdDiff step second = fun _ ↦ secondChange) :
    (fwdDiff step)^[2] (fun frequency ↦ first frequency * second frequency) =
      fun _ ↦ 2 * firstChange * secondChange := by
  funext frequency
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  have hfirstCurrent := congrFun hfirst frequency
  have hfirstNext := congrFun hfirst (frequency + step)
  have hsecondCurrent := congrFun hsecond frequency
  have hsecondNext := congrFun hsecond (frequency + step)
  simp only [fwdDiff] at hfirstCurrent hfirstNext hsecondCurrent hsecondNext
  rw [show frequency + step + step = (frequency + step) + step by rfl]
  have hfirstOne : first (frequency + step) = first frequency + firstChange := by
    linear_combination hfirstCurrent
  have hfirstTwo : first (frequency + step + step) =
      first frequency + 2 * firstChange := by
    linear_combination hfirstCurrent + hfirstNext
  have hsecondOne : second (frequency + step) = second frequency + secondChange := by
    linear_combination hsecondCurrent
  have hsecondTwo : second (frequency + step + step) =
      second frequency + 2 * secondChange := by
    linear_combination hsecondCurrent + hsecondNext
  rw [hfirstOne, hfirstTwo, hsecondOne, hsecondTwo]
  ring

/-- Mixed first differences of a product of two affine lattice readings. -/
theorem fwdDiff_fwdDiff_mul_of_linear
    (firstStep secondStep : SpatialFrequency)
    (first second : SpatialFrequency → ℂ)
    (firstChangeFirst firstChangeSecond secondChangeFirst secondChangeSecond : ℂ)
    (hfirstFirst : fwdDiff firstStep first = fun _ ↦ firstChangeFirst)
    (hfirstSecond : fwdDiff secondStep first = fun _ ↦ firstChangeSecond)
    (hsecondFirst : fwdDiff firstStep second = fun _ ↦ secondChangeFirst)
    (hsecondSecond : fwdDiff secondStep second = fun _ ↦ secondChangeSecond) :
    fwdDiff firstStep (fwdDiff secondStep
      (fun frequency ↦ first frequency * second frequency)) =
      fun _ ↦ firstChangeFirst * secondChangeSecond +
        firstChangeSecond * secondChangeFirst := by
  funext frequency
  simp only [fwdDiff]
  have hfirstFirstCurrent := congrFun hfirstFirst frequency
  have hfirstSecondCurrent := congrFun hfirstSecond frequency
  have hfirstSecondShift := congrFun hfirstSecond (frequency + firstStep)
  have hsecondFirstCurrent := congrFun hsecondFirst frequency
  have hsecondSecondCurrent := congrFun hsecondSecond frequency
  have hsecondSecondShift := congrFun hsecondSecond (frequency + firstStep)
  simp only [fwdDiff] at hfirstFirstCurrent hfirstSecondCurrent hfirstSecondShift
  simp only [fwdDiff] at hsecondFirstCurrent hsecondSecondCurrent hsecondSecondShift
  have hfirstOne : first (frequency + firstStep) =
      first frequency + firstChangeFirst := by
    linear_combination hfirstFirstCurrent
  have hfirstTwo : first (frequency + secondStep) =
      first frequency + firstChangeSecond := by
    linear_combination hfirstSecondCurrent
  have hfirstMixed : first (frequency + firstStep + secondStep) =
      first frequency + firstChangeFirst + firstChangeSecond := by
    linear_combination hfirstFirstCurrent + hfirstSecondShift
  have hsecondOne : second (frequency + firstStep) =
      second frequency + secondChangeFirst := by
    linear_combination hsecondFirstCurrent
  have hsecondTwo : second (frequency + secondStep) =
      second frequency + secondChangeSecond := by
    linear_combination hsecondSecondCurrent
  have hsecondMixed : second (frequency + firstStep + secondStep) =
      second frequency + secondChangeFirst + secondChangeSecond := by
    linear_combination hsecondFirstCurrent + hsecondSecondShift
  rw [hfirstOne, hfirstTwo, hfirstMixed, hsecondOne, hsecondTwo, hsecondMixed]
  ring

/-! ## Exact quadratic-numerator variation -/

/-- Every coordinate of a unit lattice step has norm at most one. -/
theorem norm_coordinateStep_le_one (axis other : Fin 3) :
    ‖(coordinateStep axis other : ℂ)‖ ≤ 1 := by
  fin_cases axis <;> fin_cases other <;> simp [coordinateStep]

/-- Every cross-basis reading of a unit lattice step has norm at most one. -/
theorem norm_hodgeCrossBasisFactor_coordinateStep_le_one
    (axis component input : Fin 3) :
    ‖hodgeCrossBasisFactor (coordinateStep axis) component input‖ ≤ 1 := by
  exact norm_hodgeCrossBasisFactor_le (by norm_num)
    (coordinateStep axis) (norm_coordinateStep_le_one axis) component input

/-- Any third finite difference of the quadratic Hodge numerator vanishes. -/
theorem hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    mixedForwardDifference first second 1 2
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency = 0 := by
  unfold mixedForwardDifference
  rw [show (fwdDiff (coordinateStep second))^[2]
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) =
    fun _ ↦ -(2 * (if second = coordinate then 1 else 0) *
      hodgeCrossBasisFactor (coordinateStep second) component input) by
    rw [show (fun current ↦ hodgeJacobianRatioNumerator current
          component coordinate input) =
      fun current ↦ -((current coordinate : ℂ) *
        hodgeCrossBasisFactor current component input) by rfl]
    have hproduct := fwdDiff_iter_two_mul_of_linear (coordinateStep second)
      (fun current ↦ (current coordinate : ℂ))
      (fun current ↦ hodgeCrossBasisFactor current component input)
      (if second = coordinate then 1 else 0)
      (hodgeCrossBasisFactor (coordinateStep second) component input)
      (fwdDiff_coordinate_eq second coordinate)
      (fwdDiff_hodgeCrossBasisFactor_eq second component input)
    rw [show (fun current ↦ -((current coordinate : ℂ) *
          hodgeCrossBasisFactor current component input)) =
      (-1 : ℂ) • (fun current ↦ (current coordinate : ℂ) *
        hodgeCrossBasisFactor current component input) by
      funext current
      simp]
    rw [fwdDiff_iter_const_smul, hproduct]
    funext current
    by_cases h : second = coordinate <;> simp [h]]
  simp [fwdDiff]

/-- Every mixed first/first numerator difference has norm at most two. -/
theorem norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 1 1
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency‖ ≤ 2 := by
  unfold mixedForwardDifference
  simp only [Function.iterate_one]
  rw [show (fun current ↦ hodgeJacobianRatioNumerator current
      component coordinate input) =
    fun current ↦ -((current coordinate : ℂ) *
      hodgeCrossBasisFactor current component input) by rfl]
  have hproduct := fwdDiff_fwdDiff_mul_of_linear
    (coordinateStep first) (coordinateStep second)
    (fun current ↦ (current coordinate : ℂ))
    (fun current ↦ hodgeCrossBasisFactor current component input)
    (if first = coordinate then 1 else 0)
    (if second = coordinate then 1 else 0)
    (hodgeCrossBasisFactor (coordinateStep first) component input)
    (hodgeCrossBasisFactor (coordinateStep second) component input)
    (fwdDiff_coordinate_eq first coordinate)
    (fwdDiff_coordinate_eq second coordinate)
    (fwdDiff_hodgeCrossBasisFactor_eq first component input)
    (fwdDiff_hodgeCrossBasisFactor_eq second component input)
  rw [show (fun current ↦ -((current coordinate : ℂ) *
        hodgeCrossBasisFactor current component input)) =
    (-1 : ℂ) • (fun current ↦ (current coordinate : ℂ) *
      hodgeCrossBasisFactor current component input) by
    funext current
    simp]
  rw [fwdDiff_const_smul, fwdDiff_const_smul, hproduct]
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul, norm_neg,
    ite_mul, one_mul, zero_mul]
  calc
    ‖(if first = coordinate then
          hodgeCrossBasisFactor (coordinateStep second) component input else 0) +
        (if second = coordinate then
          hodgeCrossBasisFactor (coordinateStep first) component input else 0)‖ ≤
      ‖if first = coordinate then
          hodgeCrossBasisFactor (coordinateStep second) component input else 0‖ +
        ‖if second = coordinate then
          hodgeCrossBasisFactor (coordinateStep first) component input else 0‖ :=
      norm_add_le _ _
    _ ≤ 1 + 1 := by
      gcongr
      · split_ifs
        · exact norm_hodgeCrossBasisFactor_coordinateStep_le_one
            second component input
        · simp
      · split_ifs
        · exact norm_hodgeCrossBasisFactor_coordinateStep_le_one
            first component input
        · simp
    _ = 2 := by norm_num

/-! ## Normed forward-product calculus -/

/-- One forward difference of a product, with the transported second factor retained. -/
theorem norm_fwdDiff_mul_le
    (step : SpatialFrequency) (first second : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    ‖fwdDiff step (fun current ↦ first current * second current) frequency‖ ≤
      ‖fwdDiff step first frequency‖ * ‖second (frequency + step)‖ +
        ‖first frequency‖ * ‖fwdDiff step second frequency‖ := by
  simp only [fwdDiff]
  rw [show first (frequency + step) * second (frequency + step) -
      first frequency * second frequency =
    (first (frequency + step) - first frequency) * second (frequency + step) +
      first frequency * (second (frequency + step) - second frequency) by ring]
  simpa only [norm_mul] using
    norm_add_le
      ((first (frequency + step) - first frequency) * second (frequency + step))
      (first frequency * (second (frequency + step) - second frequency))

/-- Two forward differences of a product, retaining the exact shifted first-difference
interaction. -/
theorem norm_fwdDiff_iter_two_mul_le
    (step : SpatialFrequency) (first second : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    ‖(fwdDiff step)^[2]
        (fun current ↦ first current * second current) frequency‖ ≤
      ‖(fwdDiff step)^[2] first frequency‖ *
          ‖second (frequency + step + step)‖ +
        2 * ‖fwdDiff step first frequency‖ *
          ‖fwdDiff step second (frequency + step)‖ +
        ‖first frequency‖ * ‖(fwdDiff step)^[2] second frequency‖ := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  rw [show first (frequency + step + step) * second (frequency + step + step) -
        first (frequency + step) * second (frequency + step) -
          (first (frequency + step) * second (frequency + step) -
            first frequency * second frequency) =
      first (frequency + step + step) * second (frequency + step + step) -
        2 * (first (frequency + step) * second (frequency + step)) +
          first frequency * second frequency by ring]
  rw [show first (frequency + step + step) - first (frequency + step) -
        (first (frequency + step) - first frequency) =
      first (frequency + step + step) - 2 * first (frequency + step) +
        first frequency by ring]
  rw [show second (frequency + step + step) - second (frequency + step) -
        (second (frequency + step) - second frequency) =
      second (frequency + step + step) - 2 * second (frequency + step) +
        second frequency by ring]
  rw [show
    first (frequency + step + step) * second (frequency + step + step) -
        2 * (first (frequency + step) * second (frequency + step)) +
        first frequency * second frequency =
      (first (frequency + step + step) - 2 * first (frequency + step) +
          first frequency) * second (frequency + step + step) +
        2 * (first (frequency + step) - first frequency) *
          (second (frequency + step + step) - second (frequency + step)) +
        first frequency *
          (second (frequency + step + step) - 2 * second (frequency + step) +
            second frequency) by ring]
  calc
    ‖(first (frequency + step + step) - 2 * first (frequency + step) +
          first frequency) * second (frequency + step + step) +
        2 * (first (frequency + step) - first frequency) *
          (second (frequency + step + step) - second (frequency + step)) +
        first frequency *
          (second (frequency + step + step) - 2 * second (frequency + step) +
            second frequency)‖ ≤
      ‖(first (frequency + step + step) - 2 * first (frequency + step) +
          first frequency) * second (frequency + step + step)‖ +
        ‖2 * (first (frequency + step) - first frequency) *
          (second (frequency + step + step) - second (frequency + step))‖ +
        ‖first frequency *
          (second (frequency + step + step) - 2 * second (frequency + step) +
            second frequency)‖ := by
              calc
                ‖((first (frequency + step + step) - 2 * first (frequency + step) +
                      first frequency) * second (frequency + step + step) +
                    2 * (first (frequency + step) - first frequency) *
                      (second (frequency + step + step) - second (frequency + step))) +
                    first frequency *
                      (second (frequency + step + step) - 2 * second (frequency + step) +
                        second frequency)‖ ≤
                    ‖(first (frequency + step + step) - 2 * first (frequency + step) +
                      first frequency) * second (frequency + step + step) +
                      2 * (first (frequency + step) - first frequency) *
                        (second (frequency + step + step) - second (frequency + step))‖ +
                    ‖first frequency *
                      (second (frequency + step + step) - 2 * second (frequency + step) +
                        second frequency)‖ := norm_add_le _ _
                _ ≤
                    (‖(first (frequency + step + step) - 2 * first (frequency + step) +
                      first frequency) * second (frequency + step + step)‖ +
                      ‖2 * (first (frequency + step) - first frequency) *
                        (second (frequency + step + step) - second (frequency + step))‖) +
                    ‖first frequency *
                      (second (frequency + step + step) - 2 * second (frequency + step) +
                        second frequency)‖ := by
                          gcongr
                          exact norm_add_le _ _
    _ = ‖first (frequency + step + step) - 2 * first (frequency + step) +
            first frequency‖ * ‖second (frequency + step + step)‖ +
        2 * ‖first (frequency + step) - first frequency‖ *
          ‖second (frequency + step + step) - second (frequency + step)‖ +
        ‖first frequency‖ *
          ‖second (frequency + step + step) - 2 * second (frequency + step) +
            second frequency‖ := by norm_num

/-- Exact two-step discrete Leibniz identity in a form which retains every transported factor. -/
theorem fwdDiff_iter_two_mul_eq
    (step : SpatialFrequency) (first second : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    (fwdDiff step)^[2]
        (fun current ↦ first current * second current) frequency =
      (fwdDiff step)^[2] first frequency *
          second (frequency + step + step) +
        2 * fwdDiff step first frequency *
          fwdDiff step second (frequency + step) +
        first frequency * (fwdDiff step)^[2] second frequency := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  ring

/-- Forward difference commutes with translation on the frequency lattice. -/
theorem fwdDiff_translate
    (step offset : SpatialFrequency) (coefficient : SpatialFrequency → ℂ) :
    fwdDiff step (fun frequency ↦ coefficient (frequency + offset)) =
      fun frequency ↦ fwdDiff step coefficient (frequency + offset) := by
  funext frequency
  simp only [fwdDiff]
  rw [add_right_comm frequency offset step]

/-- Two forward differences commute with translation on the frequency lattice. -/
theorem fwdDiff_iter_two_translate
    (step offset : SpatialFrequency) (coefficient : SpatialFrequency → ℂ) :
    (fwdDiff step)^[2] (fun frequency ↦ coefficient (frequency + offset)) =
      fun frequency ↦ (fwdDiff step)^[2] coefficient (frequency + offset) := by
  funext frequency
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  rw [add_right_comm frequency offset step,
    add_right_comm (frequency + step) offset step]

/-- Exact nine-term Leibniz expansion for two forward differences in each of two directions. -/
theorem mixedForwardDifference_two_two_mul_eq
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 2 2
        (fun current ↦ left current * right current) frequency =
      mixedForwardDifference first second 2 2 left frequency *
          right (frequency + coordinateStep second + coordinateStep second +
            coordinateStep first + coordinateStep first) +
      (2 * mixedForwardDifference first second 1 2 left frequency *
          mixedForwardDifference first second 1 0 right
            (frequency + coordinateStep second + coordinateStep second +
              coordinateStep first)) +
      (mixedForwardDifference first second 0 2 left frequency *
          mixedForwardDifference first second 2 0 right
            (frequency + coordinateStep second + coordinateStep second)) +
      (2 * mixedForwardDifference first second 2 1 left frequency *
          mixedForwardDifference first second 0 1 right
            (frequency + coordinateStep first + coordinateStep first +
              coordinateStep second)) +
      (4 * mixedForwardDifference first second 1 1 left frequency *
          mixedForwardDifference first second 1 1 right
            (frequency + coordinateStep first + coordinateStep second)) +
      (2 * mixedForwardDifference first second 0 1 left frequency *
          mixedForwardDifference first second 2 1 right
            (frequency + coordinateStep second)) +
      (mixedForwardDifference first second 2 0 left frequency *
          mixedForwardDifference first second 0 2 right
            (frequency + coordinateStep first + coordinateStep first)) +
      (2 * mixedForwardDifference first second 1 0 left frequency *
          mixedForwardDifference first second 1 2 right
            (frequency + coordinateStep first)) +
      left frequency *
        mixedForwardDifference first second 2 2 right frequency := by
  let firstStep := coordinateStep first
  let secondStep := coordinateStep second
  let firstTerm : SpatialFrequency → ℂ := fun current ↦
    (fwdDiff secondStep)^[2] left current *
      right (current + secondStep + secondStep)
  let middleTerm : SpatialFrequency → ℂ := fun current ↦
    fwdDiff secondStep left current *
      fwdDiff secondStep right (current + secondStep)
  let lastTerm : SpatialFrequency → ℂ := fun current ↦
    left current * (fwdDiff secondStep)^[2] right current
  have hsecondProduct :
      (fwdDiff secondStep)^[2]
          (fun current ↦ left current * right current) =
        firstTerm + (2 : ℂ) • middleTerm + lastTerm := by
    funext current
    simpa [firstTerm, middleTerm, lastTerm, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, mul_assoc] using
        fwdDiff_iter_two_mul_eq secondStep left right current
  unfold mixedForwardDifference
  rw [hsecondProduct, fwdDiff_iter_add, fwdDiff_iter_add,
    fwdDiff_iter_const_smul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change
    (fwdDiff firstStep)^[2]
          (fun current ↦ (fwdDiff secondStep)^[2] left current *
            right (current + secondStep + secondStep)) frequency +
      2 * (fwdDiff firstStep)^[2]
          (fun current ↦ fwdDiff secondStep left current *
            fwdDiff secondStep right (current + secondStep)) frequency +
      (fwdDiff firstStep)^[2]
          (fun current ↦ left current *
            (fwdDiff secondStep)^[2] right current) frequency = _
  rw [fwdDiff_iter_two_mul_eq firstStep
      ((fwdDiff secondStep)^[2] left)
      (fun current ↦ right (current + secondStep + secondStep)) frequency,
    fwdDiff_iter_two_mul_eq firstStep
      (fwdDiff secondStep left)
      (fun current ↦ fwdDiff secondStep right (current + secondStep)) frequency,
    fwdDiff_iter_two_mul_eq firstStep left
      ((fwdDiff secondStep)^[2] right) frequency]
  rw [show (fun current ↦ right (current + secondStep + secondStep)) =
      fun current ↦ right (current + (secondStep + secondStep)) by
        funext current
        rw [add_assoc],
    congrFun (fwdDiff_translate firstStep (secondStep + secondStep) right)
      (frequency + firstStep),
    congrFun (fwdDiff_iter_two_translate firstStep
      (secondStep + secondStep) right) frequency,
    congrFun (fwdDiff_translate firstStep secondStep
      (fwdDiff secondStep right)) (frequency + firstStep),
    congrFun (fwdDiff_iter_two_translate firstStep secondStep
      (fwdDiff secondStep right)) frequency]
  dsimp [firstStep, secondStep]
  rw [show frequency + coordinateStep first + coordinateStep first +
          coordinateStep second + coordinateStep second =
        frequency + coordinateStep second + coordinateStep second +
          coordinateStep first + coordinateStep first by abel,
    show frequency + coordinateStep first +
          (coordinateStep second + coordinateStep second) =
        frequency + coordinateStep second + coordinateStep second +
          coordinateStep first by abel,
    show frequency + (coordinateStep second + coordinateStep second) =
        frequency + coordinateStep second + coordinateStep second by abel]
  ring

/-- Triangle receiver for the exact nine-corner mixed Leibniz population. -/
theorem norm_add_nine_le
    (a b c d e f g h i : ℂ) :
    ‖a + (b + (c + (d + (e + (f + (g + (h + i)))))))‖ ≤
      ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + (‖g‖ + (‖h‖ + ‖i‖))))))) := by
  calc
    ‖a + (b + (c + (d + (e + (f + (g + (h + i)))))))‖ ≤
        ‖a‖ + ‖b + (c + (d + (e + (f + (g + (h + i))))))‖ := norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + ‖c + (d + (e + (f + (g + (h + i)))))‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + ‖d + (e + (f + (g + (h + i))))‖)) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + ‖e + (f + (g + (h + i)))‖))) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + ‖f + (g + (h + i))‖)))) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + ‖g + (h + i)‖))))) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + (‖g‖ + ‖h + i‖)))))) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + (‖g‖ + (‖h‖ + ‖i‖))))))) := by
      gcongr
      exact norm_add_le _ _

/-- Forward differences along two lattice translations commute exactly. -/
theorem fwdDiff_comm
    (firstStep secondStep : SpatialFrequency)
    (coefficient : SpatialFrequency → ℂ) :
    fwdDiff firstStep (fwdDiff secondStep coefficient) =
      fwdDiff secondStep (fwdDiff firstStep coefficient) := by
  funext frequency
  simp only [fwdDiff]
  rw [add_right_comm frequency firstStep secondStep]
  ring

/-- One forward difference commutes through two differences in a transverse direction. -/
theorem fwdDiff_iter_two_comm
    (firstStep secondStep : SpatialFrequency)
    (coefficient : SpatialFrequency → ℂ) :
    fwdDiff firstStep ((fwdDiff secondStep)^[2] coefficient) =
      (fwdDiff secondStep)^[2] (fwdDiff firstStep coefficient) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  rw [fwdDiff_comm firstStep secondStep (fwdDiff secondStep coefficient),
    fwdDiff_comm firstStep secondStep coefficient]

/-- Two differences in each of two directions commute exactly. -/
theorem fwdDiff_iter_two_iter_two_comm
    (firstStep secondStep : SpatialFrequency)
    (coefficient : SpatialFrequency → ℂ) :
    (fwdDiff firstStep)^[2] ((fwdDiff secondStep)^[2] coefficient) =
      (fwdDiff secondStep)^[2] ((fwdDiff firstStep)^[2] coefficient) := by
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply]
  calc
    fwdDiff firstStep
        (fwdDiff firstStep (fwdDiff secondStep (fwdDiff secondStep coefficient))) =
      fwdDiff firstStep
        (fwdDiff secondStep (fwdDiff secondStep (fwdDiff firstStep coefficient))) :=
      congrArg (fwdDiff firstStep)
        (fwdDiff_iter_two_comm firstStep secondStep coefficient)
    _ = fwdDiff secondStep
        (fwdDiff secondStep (fwdDiff firstStep (fwdDiff firstStep coefficient))) :=
      fwdDiff_iter_two_comm firstStep secondStep (fwdDiff firstStep coefficient)

/-- The addressed point in a finite two-axis forward stencil. -/
def twoAxisStencilPoint
    (first second : Fin 3) (frequency : SpatialFrequency) (i j : ℕ) :
    SpatialFrequency :=
  frequency + i • coordinateStep first + j • coordinateStep second

/-- Genuine geometric control of a finite two-axis stencil: every displayed point retains a
positive quadratic denominator and an explicit coordinate aperture. -/
def TwoAxisStencilControlled
    (lower bound : ℝ) (first second : Fin 3) (frequency : SpatialFrequency)
    (firstOrder secondOrder : ℕ) : Prop :=
  ∀ i ≤ firstOrder, ∀ j ≤ secondOrder,
    lower ≤ frequencySquared (twoAxisStencilPoint first second frequency i j) ∧
      ∀ other : Fin 3,
        ‖(twoAxisStencilPoint first second frequency i j other : ℂ)‖ ≤ bound

@[simp]
theorem twoAxisStencilPoint_zero_zero
    (first second : Fin 3) (frequency : SpatialFrequency) :
    twoAxisStencilPoint first second frequency 0 0 = frequency := by
  simp [twoAxisStencilPoint]

/-- Advancing the first stencil index is genuine translation in its addressed coordinate. -/
theorem twoAxisStencilPoint_succ_first
    (first second : Fin 3) (frequency : SpatialFrequency) (i j : ℕ) :
    twoAxisStencilPoint first second frequency (i + 1) j =
      twoAxisStencilPoint first second frequency i j + coordinateStep first := by
  unfold twoAxisStencilPoint
  rw [add_nsmul]
  simp only [one_nsmul]
  abel

/-- Advancing the second stencil index is genuine translation in its addressed coordinate. -/
theorem twoAxisStencilPoint_succ_second
    (first second : Fin 3) (frequency : SpatialFrequency) (i j : ℕ) :
    twoAxisStencilPoint first second frequency i (j + 1) =
      twoAxisStencilPoint first second frequency i j + coordinateStep second := by
  unfold twoAxisStencilPoint
  rw [add_nsmul]
  simp only [one_nsmul]
  abel

/-- Rebasing a rectangular stencil adds its two natural offsets. -/
theorem twoAxisStencilPoint_rebase
    (first second : Fin 3) (frequency : SpatialFrequency)
    (firstOffset secondOffset i j : ℕ) :
    twoAxisStencilPoint first second
        (twoAxisStencilPoint first second frequency firstOffset secondOffset) i j =
      twoAxisStencilPoint first second frequency
        (firstOffset + i) (secondOffset + j) := by
  unfold twoAxisStencilPoint
  rw [add_nsmul, add_nsmul]
  abel

/-- Every addressed subrectangle inherits the genuine denominator and aperture control of its
parent stencil. -/
theorem TwoAxisStencilControlled.rebase
    {lower bound : ℝ} {first second : Fin 3} {frequency : SpatialFrequency}
    {firstTotal secondTotal firstOffset secondOffset firstOrder secondOrder : ℕ}
    (hstencil : TwoAxisStencilControlled lower bound first second frequency
      firstTotal secondTotal)
    (hfirst : firstOffset + firstOrder ≤ firstTotal)
    (hsecond : secondOffset + secondOrder ≤ secondTotal) :
    TwoAxisStencilControlled lower bound first second
      (twoAxisStencilPoint first second frequency firstOffset secondOffset)
      firstOrder secondOrder := by
  intro i hi j hj
  rw [twoAxisStencilPoint_rebase]
  exact hstencil (firstOffset + i) (by omega) (secondOffset + j) (by omega)

/-- Swapping the two displayed axes transposes the same controlled stencil. -/
theorem TwoAxisStencilControlled.transpose
    {lower bound : ℝ} {first second : Fin 3} {frequency : SpatialFrequency}
    {firstOrder secondOrder : ℕ}
    (hstencil : TwoAxisStencilControlled lower bound first second frequency
      firstOrder secondOrder) :
    TwoAxisStencilControlled lower bound second first frequency
      secondOrder firstOrder := by
  intro i hi j hj
  have hpoint : twoAxisStencilPoint second first frequency i j =
      twoAxisStencilPoint first second frequency j i := by
    unfold twoAxisStencilPoint
    abel
  rw [hpoint]
  exact hstencil j hj i hi

/-! ## Reciprocal envelopes on a thickened annular stencil -/

/-- Reciprocal of the genuine quadratic Hodge denominator, totalized at zero exactly as complex
division. -/
def hodgeReciprocal (frequency : SpatialFrequency) : ℂ :=
  1 / (frequencySquared frequency : ℂ)

/-- Exact first reciprocal passage along one lattice coordinate. -/
theorem fwdDiff_hodgeReciprocal_eq
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hcurrent : frequencySquared frequency ≠ 0)
    (hnext : frequencySquared (frequency + coordinateStep axis) ≠ 0) :
    fwdDiff (coordinateStep axis) hodgeReciprocal frequency =
      -((frequencySquared (frequency + coordinateStep axis) -
          frequencySquared frequency : ℝ) : ℂ) *
        hodgeReciprocal (frequency + coordinateStep axis) *
          hodgeReciprocal frequency := by
  unfold fwdDiff hodgeReciprocal
  have hcurrentComplex : (frequencySquared frequency : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hcurrent
  have hnextComplex :
      (frequencySquared (frequency + coordinateStep axis) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnext
  field_simp [hcurrentComplex, hnextComplex]
  push_cast
  ring

/-- The quadratic-denominator first change is invariant under a distinct coordinate step. -/
theorem frequencySquared_change_add_distinct
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) :
    frequencySquared (frequency + coordinateStep second + coordinateStep first) -
        frequencySquared (frequency + coordinateStep second) =
      frequencySquared (frequency + coordinateStep first) -
        frequencySquared frequency := by
  rw [add_coordinateStep_eq_increment, add_coordinateStep_eq_increment,
    add_coordinateStep_eq_increment,
    frequencySquared_incrementFrequencyCoordinate,
    frequencySquared_incrementFrequencyCoordinate,
    frequencySquared_incrementFrequencyCoordinate,
    incrementFrequencyCoordinate_apply_of_ne haxes]
  ring

/-- A two-step denominator span in one axis is invariant under a distinct transverse step. -/
theorem frequencySquared_twoStepSpan_add_distinct
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) :
    frequencySquared
          (frequency + coordinateStep second + coordinateStep first +
            coordinateStep first) -
        frequencySquared (frequency + coordinateStep second) =
      frequencySquared (frequency + coordinateStep first + coordinateStep first) -
        frequencySquared frequency := by
  fin_cases first <;> fin_cases second <;>
    simp at haxes ⊢ <;>
    simp [coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- Two steps in one coordinate change the quadratic denominator by at most `4 bound + 4`. -/
theorem abs_frequencySquared_add_two_coordinateStep_sub_le
    {bound : ℝ}
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound) :
    |frequencySquared (frequency + coordinateStep axis + coordinateStep axis) -
        frequencySquared frequency| ≤ 4 * bound + 4 := by
  rw [add_coordinateStep_eq_increment, add_coordinateStep_eq_increment,
    frequencySquared_incrementFrequencyCoordinate,
    frequencySquared_incrementFrequencyCoordinate,
    incrementFrequencyCoordinate_apply_same]
  have haxis : |(frequency axis : ℝ)| ≤ bound := by
    simpa [Complex.norm_intCast] using hcoordinates axis
  push_cast
  rw [show frequencySquared frequency + 2 * (frequency axis : ℝ) + 1 +
        2 * ((frequency axis : ℝ) + 1) + 1 - frequencySquared frequency =
      4 * (frequency axis : ℝ) + 4 by ring]
  calc
    |4 * (frequency axis : ℝ) + 4| ≤
        |4 * (frequency axis : ℝ)| + |(4 : ℝ)| := abs_add_le _ _
    _ = 4 * |(frequency axis : ℝ)| + 4 := by simp
    _ ≤ 4 * bound + 4 := by gcongr

/-! ## Quantitative reciprocal transport -/

/-- A positive lower bound on the genuine quadratic denominator controls its complex reciprocal. -/
theorem norm_hodgeReciprocal_le
    {lower : ℝ} (hlower : 0 < lower) (frequency : SpatialFrequency)
    (hfrequency : lower ≤ frequencySquared frequency) :
    ‖hodgeReciprocal frequency‖ ≤ 1 / lower := by
  have hpositive : 0 < frequencySquared frequency := hlower.trans_le hfrequency
  rw [hodgeReciprocal, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hpositive]
  exact div_le_div_of_nonneg_left (by norm_num) hlower hfrequency

/-- One genuine reciprocal difference has its exact first-order scale. -/
theorem norm_fwdDiff_hodgeReciprocal_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hcurrent : lower ≤ frequencySquared frequency)
    (hnext : lower ≤
      frequencySquared (frequency + coordinateStep axis)) :
    ‖fwdDiff (coordinateStep axis) hodgeReciprocal frequency‖ ≤
      (2 * bound + 1) / lower ^ 2 := by
  have hcurrentPositive : 0 < frequencySquared frequency :=
    hlower.trans_le hcurrent
  have hnextPositive :
      0 < frequencySquared (frequency + coordinateStep axis) :=
    hlower.trans_le hnext
  have hchange :
      |frequencySquared (frequency + coordinateStep axis) -
          frequencySquared frequency| ≤ 2 * bound + 1 := by
    rw [add_coordinateStep_eq_increment]
    exact abs_frequencySquared_increment_sub_le hbound frequency hcoordinates axis
  rw [fwdDiff_hodgeReciprocal_eq axis frequency
    hcurrentPositive.ne' hnextPositive.ne', norm_mul, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    |frequencySquared (frequency + coordinateStep axis) -
          frequencySquared frequency| *
          ‖hodgeReciprocal (frequency + coordinateStep axis)‖ *
            ‖hodgeReciprocal frequency‖ ≤
      (2 * bound + 1) * (1 / lower) * (1 / lower) := by
        gcongr
        · exact norm_hodgeReciprocal_le hlower _ hnext
        · exact norm_hodgeReciprocal_le hlower _ hcurrent
    _ = (2 * bound + 1) / lower ^ 2 := by ring

/-- Same-axis reciprocal curvature with the quadratic `2` residue and the exact span change kept
separate. -/
theorem norm_fwdDiff_iter_two_hodgeReciprocal_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hfirst : lower ≤ frequencySquared frequency)
    (hmiddle : lower ≤ frequencySquared (frequency + coordinateStep axis))
    (hlast : lower ≤
      frequencySquared (frequency + coordinateStep axis + coordinateStep axis)) :
    ‖(fwdDiff (coordinateStep axis))^[2] hodgeReciprocal frequency‖ ≤
      2 / lower ^ 2 +
        ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3 := by
  have hfirstPositive : 0 < frequencySquared frequency := hlower.trans_le hfirst
  have hmiddlePositive :
      0 < frequencySquared (frequency + coordinateStep axis) :=
    hlower.trans_le hmiddle
  have hlastPositive :
      0 < frequencySquared
        (frequency + coordinateStep axis + coordinateStep axis) :=
    hlower.trans_le hlast
  have hfirstChange :
      |frequencySquared (frequency + coordinateStep axis) -
          frequencySquared frequency| ≤ 2 * bound + 1 := by
    rw [add_coordinateStep_eq_increment]
    exact abs_frequencySquared_increment_sub_le hbound frequency hcoordinates axis
  have hspanChange :
      |frequencySquared (frequency + coordinateStep axis + coordinateStep axis) -
          frequencySquared frequency| ≤ 4 * bound + 4 := by
    rw [add_coordinateStep_eq_increment, add_coordinateStep_eq_increment,
      frequencySquared_incrementFrequencyCoordinate,
      frequencySquared_incrementFrequencyCoordinate,
      incrementFrequencyCoordinate_apply_same]
    have haxis : |(frequency axis : ℝ)| ≤ bound := by
      simpa [Complex.norm_intCast] using hcoordinates axis
    push_cast
    rw [show frequencySquared frequency + 2 * (frequency axis : ℝ) + 1 +
          2 * ((frequency axis : ℝ) + 1) + 1 -
            frequencySquared frequency =
        4 * (frequency axis : ℝ) + 4 by ring]
    calc
      |4 * (frequency axis : ℝ) + 4| ≤
          |4 * (frequency axis : ℝ)| + |(4 : ℝ)| := abs_add_le _ _
      _ = 4 * |(frequency axis : ℝ)| + 4 := by simp
      _ ≤ 4 * bound + 4 := by gcongr
  have hsecondChange :
      |frequencySquared (frequency + coordinateStep axis + coordinateStep axis) -
          2 * frequencySquared (frequency + coordinateStep axis) +
            frequencySquared frequency| ≤ 2 := by
    rw [add_coordinateStep_eq_increment, add_coordinateStep_eq_increment,
      show frequencySquared
          (incrementFrequencyCoordinate axis
            (incrementFrequencyCoordinate axis frequency)) -
          2 * frequencySquared (incrementFrequencyCoordinate axis frequency) +
            frequencySquared frequency = 2 by
        exact frequencySquared_secondDifference_eq_two axis frequency]
    norm_num
  have hreal := abs_reciprocal_secondDifference_le
    (frequencySquared frequency)
    (frequencySquared (frequency + coordinateStep axis))
    (frequencySquared (frequency + coordinateStep axis + coordinateStep axis))
    lower (2 * bound + 1) (4 * bound + 4) 2
    hlower hfirst hmiddle hlast hfirstChange hspanChange hsecondChange
    (by positivity) (by positivity) (by norm_num)
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
  have hcast :
      hodgeReciprocal (frequency + coordinateStep axis + coordinateStep axis) -
          hodgeReciprocal (frequency + coordinateStep axis) -
            (hodgeReciprocal (frequency + coordinateStep axis) -
              hodgeReciprocal frequency) =
        ((1 / frequencySquared
              (frequency + coordinateStep axis + coordinateStep axis) -
            2 / frequencySquared (frequency + coordinateStep axis) +
              1 / frequencySquared frequency : ℝ) : ℂ) := by
    simp [hodgeReciprocal, div_eq_mul_inv]
    ring
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  exact hreal

/-- Exact same-axis reciprocal curvature, separated into the quadratic `2` residue and the
three-reciprocal span interaction. -/
theorem fwdDiff_iter_two_hodgeReciprocal_eq
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hfirst : frequencySquared frequency ≠ 0)
    (hmiddle : frequencySquared (frequency + coordinateStep axis) ≠ 0)
    (hlast : frequencySquared
      (frequency + coordinateStep axis + coordinateStep axis) ≠ 0) :
    (fwdDiff (coordinateStep axis))^[2] hodgeReciprocal frequency =
      -2 * hodgeReciprocal
          (frequency + coordinateStep axis + coordinateStep axis) *
            hodgeReciprocal (frequency + coordinateStep axis) +
        ((frequencySquared (frequency + coordinateStep axis) -
            frequencySquared frequency : ℝ) : ℂ) *
          ((frequencySquared
              (frequency + coordinateStep axis + coordinateStep axis) -
            frequencySquared frequency : ℝ) : ℂ) *
          hodgeReciprocal frequency *
          hodgeReciprocal (frequency + coordinateStep axis) *
          hodgeReciprocal
            (frequency + coordinateStep axis + coordinateStep axis) := by
  let first := frequencySquared frequency
  let middle := frequencySquared (frequency + coordinateStep axis)
  let last := frequencySquared
    (frequency + coordinateStep axis + coordinateStep axis)
  have hreal := reciprocal_secondDifference_eq first middle last
    hfirst hmiddle hlast
  have hsecond : last - 2 * middle + first = 2 := by
    dsimp [first, middle, last]
    rw [add_coordinateStep_eq_increment, add_coordinateStep_eq_increment]
    exact frequencySquared_secondDifference_eq_two axis frequency
  rw [hsecond] at hreal
  calc
    (fwdDiff (coordinateStep axis))^[2] hodgeReciprocal frequency =
        ((1 / last - 2 / middle + 1 / first : ℝ) : ℂ) := by
          simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
          simp [hodgeReciprocal, first, middle, last, div_eq_mul_inv]
          ring
    _ = ((-2 / (last * middle) +
        (middle - first) * (last - first) / (first * middle * last) : ℝ) : ℂ) :=
      congrArg (· : ℝ → ℂ) hreal
    _ = -2 * hodgeReciprocal
          (frequency + coordinateStep axis + coordinateStep axis) *
            hodgeReciprocal (frequency + coordinateStep axis) +
        ((frequencySquared (frequency + coordinateStep axis) -
            frequencySquared frequency : ℝ) : ℂ) *
          ((frequencySquared
              (frequency + coordinateStep axis + coordinateStep axis) -
            frequencySquared frequency : ℝ) : ℂ) *
          hodgeReciprocal frequency *
          hodgeReciprocal (frequency + coordinateStep axis) *
          hodgeReciprocal
            (frequency + coordinateStep axis + coordinateStep axis) := by
      simp [hodgeReciprocal, first, middle, last, div_eq_mul_inv]
      ring

/-- Distinct-axis reciprocal mixed curvature.  The denominator change in one direction is
unchanged by the transverse step, so the four-corner passage gains three reciprocal powers. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_one_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (hcoordinatesSecond : ∀ other : Fin 3,
      ‖((frequency + coordinateStep second) other : ℂ)‖ ≤ bound)
    (hfirst : lower ≤ frequencySquared frequency)
    (hfirstNext : lower ≤ frequencySquared (frequency + coordinateStep first))
    (hsecondNext : lower ≤ frequencySquared (frequency + coordinateStep second))
    (hmixed : lower ≤
      frequencySquared (frequency + coordinateStep first + coordinateStep second)) :
    ‖mixedForwardDifference first second 1 1 hodgeReciprocal frequency‖ ≤
      2 * (2 * bound + 1) ^ 2 / lower ^ 3 := by
  have h00Positive : 0 < frequencySquared frequency := hlower.trans_le hfirst
  have h10Positive : 0 < frequencySquared (frequency + coordinateStep first) :=
    hlower.trans_le hfirstNext
  have h01Positive : 0 < frequencySquared (frequency + coordinateStep second) :=
    hlower.trans_le hsecondNext
  have h11Positive :
      0 < frequencySquared (frequency + coordinateStep first + coordinateStep second) :=
    hlower.trans_le hmixed
  have hmixed' : lower ≤
      frequencySquared (frequency + coordinateStep second + coordinateStep first) := by
    simpa [add_assoc, add_left_comm, add_comm] using hmixed
  have hx0 := norm_fwdDiff_hodgeReciprocal_le hlower hbound first frequency
    hcoordinates hfirst hfirstNext
  have hx1 := norm_fwdDiff_hodgeReciprocal_le hlower hbound first
    (frequency + coordinateStep second) hcoordinatesSecond hsecondNext hmixed'
  have hr00 := norm_hodgeReciprocal_le hlower frequency hfirst
  have hr10 := norm_hodgeReciprocal_le hlower
    (frequency + coordinateStep first) hfirstNext
  have hr01 := norm_hodgeReciprocal_le hlower
    (frequency + coordinateStep second) hsecondNext
  have hx0' :
      ‖hodgeReciprocal (frequency + coordinateStep first) -
          hodgeReciprocal frequency‖ ≤ (2 * bound + 1) / lower ^ 2 := by
    simpa [fwdDiff] using hx0
  have hx1' :
      ‖hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) -
          hodgeReciprocal (frequency + coordinateStep second)‖ ≤
        (2 * bound + 1) / lower ^ 2 := by
    simpa [add_assoc, add_left_comm, add_comm, fwdDiff] using hx1
  have hchange :
      |frequencySquared (frequency + coordinateStep second) -
          frequencySquared frequency| ≤ 2 * bound + 1 := by
    rw [add_coordinateStep_eq_increment]
    exact abs_frequencySquared_increment_sub_le hbound frequency hcoordinates second
  have hy0 := fwdDiff_hodgeReciprocal_eq second frequency
    h00Positive.ne' h01Positive.ne'
  have hy1 := fwdDiff_hodgeReciprocal_eq second
    (frequency + coordinateStep first) h10Positive.ne' h11Positive.ne'
  rw [frequencySquared_change_add_distinct second first haxes.symm frequency] at hy1
  have hidentity :
      mixedForwardDifference first second 1 1 hodgeReciprocal frequency =
        -((frequencySquared (frequency + coordinateStep second) -
            frequencySquared frequency : ℝ) : ℂ) *
          (hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) *
              hodgeReciprocal (frequency + coordinateStep first) -
            hodgeReciprocal (frequency + coordinateStep second) *
              hodgeReciprocal frequency) := by
    unfold mixedForwardDifference
    simp only [Function.iterate_one, fwdDiff]
    rw [show
      hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) -
          hodgeReciprocal (frequency + coordinateStep first) =
        fwdDiff (coordinateStep second) hodgeReciprocal
          (frequency + coordinateStep first) by rfl,
      show hodgeReciprocal (frequency + coordinateStep second) -
          hodgeReciprocal frequency =
        fwdDiff (coordinateStep second) hodgeReciprocal frequency by rfl,
      hy1, hy0]
    ring
  rw [hidentity, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  have hproduct :
      ‖hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) *
            hodgeReciprocal (frequency + coordinateStep first) -
          hodgeReciprocal (frequency + coordinateStep second) *
            hodgeReciprocal frequency‖ ≤
        2 * ((2 * bound + 1) / lower ^ 2) * (1 / lower) := by
    rw [show
      hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) *
            hodgeReciprocal (frequency + coordinateStep first) -
          hodgeReciprocal (frequency + coordinateStep second) *
            hodgeReciprocal frequency =
        (hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) -
            hodgeReciprocal (frequency + coordinateStep second)) *
              hodgeReciprocal (frequency + coordinateStep first) +
          hodgeReciprocal (frequency + coordinateStep second) *
            (hodgeReciprocal (frequency + coordinateStep first) -
              hodgeReciprocal frequency) by ring]
    calc
      ‖(hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) -
              hodgeReciprocal (frequency + coordinateStep second)) *
            hodgeReciprocal (frequency + coordinateStep first) +
          hodgeReciprocal (frequency + coordinateStep second) *
            (hodgeReciprocal (frequency + coordinateStep first) -
              hodgeReciprocal frequency)‖ ≤
        ‖hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) -
              hodgeReciprocal (frequency + coordinateStep second)‖ *
            ‖hodgeReciprocal (frequency + coordinateStep first)‖ +
          ‖hodgeReciprocal (frequency + coordinateStep second)‖ *
            ‖hodgeReciprocal (frequency + coordinateStep first) -
              hodgeReciprocal frequency‖ := by
                have hadd := norm_add_le
                  ((hodgeReciprocal
                        (frequency + coordinateStep first + coordinateStep second) -
                      hodgeReciprocal (frequency + coordinateStep second)) *
                    hodgeReciprocal (frequency + coordinateStep first))
                  (hodgeReciprocal (frequency + coordinateStep second) *
                    (hodgeReciprocal (frequency + coordinateStep first) -
                      hodgeReciprocal frequency))
                simpa only [norm_mul] using hadd
      _ ≤ ((2 * bound + 1) / lower ^ 2) * (1 / lower) +
          (1 / lower) * ((2 * bound + 1) / lower ^ 2) := by
            apply add_le_add
            · exact mul_le_mul hx1' hr10 (norm_nonneg _) (by positivity)
            · exact mul_le_mul hr01 hx0' (norm_nonneg _) (by positivity)
      _ = 2 * ((2 * bound + 1) / lower ^ 2) * (1 / lower) := by ring
  calc
    |frequencySquared (frequency + coordinateStep second) -
          frequencySquared frequency| *
        ‖hodgeReciprocal (frequency + coordinateStep first + coordinateStep second) *
              hodgeReciprocal (frequency + coordinateStep first) -
            hodgeReciprocal (frequency + coordinateStep second) *
              hodgeReciprocal frequency‖ ≤
      (2 * bound + 1) *
        (2 * ((2 * bound + 1) / lower ^ 2) * (1 / lower)) := by gcongr
    _ = 2 * (2 * bound + 1) ^ 2 / lower ^ 3 := by ring

/-- One-by-two distinct-axis reciprocal variation.  The affine denominator change is transverse
constant, leaving a second difference of a two-reciprocal product. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_one_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 2) :
    ‖mixedForwardDifference first second 1 2 hodgeReciprocal frequency‖ ≤
      (2 * bound + 1) *
        (2 * (1 / lower) *
            (2 / lower ^ 2 +
              ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
          2 * ((2 * bound + 1) / lower ^ 2) ^ 2) := by
  have h00raw := hstencil 0 (by omega) 0 (by omega)
  have h10raw := hstencil 1 (by omega) 0 (by omega)
  have h01raw := hstencil 0 (by omega) 1 (by omega)
  have h11raw := hstencil 1 (by omega) 1 (by omega)
  have h02raw := hstencil 0 (by omega) 2 (by omega)
  have h12raw := hstencil 1 (by omega) 2 (by omega)
  have h00 : lower ≤ frequencySquared frequency := by
    simpa [twoAxisStencilPoint] using h00raw.1
  have h10 : lower ≤ frequencySquared (frequency + coordinateStep first) := by
    simpa [twoAxisStencilPoint] using h10raw.1
  have h01 : lower ≤ frequencySquared (frequency + coordinateStep second) := by
    simpa [twoAxisStencilPoint] using h01raw.1
  have h11 : lower ≤
      frequencySquared (frequency + coordinateStep first + coordinateStep second) := by
    simpa [twoAxisStencilPoint] using h11raw.1
  have h02 : lower ≤
      frequencySquared (frequency + coordinateStep second + coordinateStep second) := by
    rw [← show twoAxisStencilPoint first second frequency 0 2 =
        frequency + coordinateStep second + coordinateStep second by
      funext other
      simp [twoAxisStencilPoint]
      ring]
    exact h02raw.1
  have h12 : lower ≤ frequencySquared
      (frequency + coordinateStep first + coordinateStep second + coordinateStep second) := by
    rw [← show twoAxisStencilPoint first second frequency 1 2 =
        frequency + coordinateStep first + coordinateStep second + coordinateStep second by
      funext other
      simp [twoAxisStencilPoint]
      ring]
    exact h12raw.1
  have hc00 : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using h00raw.2
  have hc10 : ∀ other : Fin 3,
      ‖((frequency + coordinateStep first) other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using h10raw.2
  have hc01 : ∀ other : Fin 3,
      ‖((frequency + coordinateStep second) other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using h01raw.2
  let firstBound := (2 * bound + 1) / lower ^ 2
  let secondBound := 2 / lower ^ 2 +
    ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3
  have hr00 := norm_hodgeReciprocal_le hlower frequency h00
  have hr10 := norm_hodgeReciprocal_le hlower
    (frequency + coordinateStep first) h10
  have hr02 := norm_hodgeReciprocal_le hlower
    (frequency + coordinateStep second + coordinateStep second) h02
  have hry0 := norm_fwdDiff_hodgeReciprocal_le hlower hbound second frequency
    hc00 h00 h01
  have hry1 := norm_fwdDiff_hodgeReciprocal_le hlower hbound second
    (frequency + coordinateStep second) hc01 h01 h02
  have hryx := norm_fwdDiff_hodgeReciprocal_le hlower hbound second
    (frequency + coordinateStep first) hc10 h10 h11
  have hryy0 := norm_fwdDiff_iter_two_hodgeReciprocal_le hlower hbound second
    frequency hc00 h00 h01 h02
  have hryyx := norm_fwdDiff_iter_two_hodgeReciprocal_le hlower hbound second
    (frequency + coordinateStep first) hc10 h10 h11 h12
  have htranslatedFirst :
      ‖fwdDiff (coordinateStep second)
          (fun current ↦ hodgeReciprocal (current + coordinateStep first)) frequency‖ ≤
        firstBound := by
    rw [congrFun (fwdDiff_translate (coordinateStep second)
      (coordinateStep first) hodgeReciprocal) frequency]
    simpa [firstBound] using hryx
  have htranslatedSecond :
      ‖(fwdDiff (coordinateStep second))^[2]
          (fun current ↦ hodgeReciprocal (current + coordinateStep first)) frequency‖ ≤
        secondBound := by
    rw [congrFun (fwdDiff_iter_two_translate (coordinateStep second)
      (coordinateStep first) hodgeReciprocal) frequency]
    simpa [secondBound] using hryyx
  have hproductRaw := norm_fwdDiff_iter_two_mul_le (coordinateStep second)
    (fun current ↦ hodgeReciprocal (current + coordinateStep first))
    hodgeReciprocal frequency
  have hproduct :
      ‖(fwdDiff (coordinateStep second))^[2]
          (fun current ↦ hodgeReciprocal (current + coordinateStep first) *
            hodgeReciprocal current) frequency‖ ≤
        2 * (1 / lower) * secondBound + 2 * firstBound ^ 2 := by
    refine hproductRaw.trans ?_
    calc
      ‖(fwdDiff (coordinateStep second))^[2]
            (fun current ↦ hodgeReciprocal (current + coordinateStep first)) frequency‖ *
            ‖hodgeReciprocal
              (frequency + coordinateStep second + coordinateStep second)‖ +
          2 *
              ‖fwdDiff (coordinateStep second)
                (fun current ↦ hodgeReciprocal (current + coordinateStep first))
                  frequency‖ *
            ‖fwdDiff (coordinateStep second) hodgeReciprocal
              (frequency + coordinateStep second)‖ +
          ‖hodgeReciprocal (frequency + coordinateStep first)‖ *
            ‖(fwdDiff (coordinateStep second))^[2] hodgeReciprocal frequency‖ ≤
        secondBound * (1 / lower) +
          2 * firstBound * firstBound +
            (1 / lower) * secondBound := by
              have hfirstTerm := mul_le_mul htranslatedSecond hr02
                (norm_nonneg _) (by positivity : 0 ≤ secondBound)
              have hmiddleFactors := mul_le_mul htranslatedFirst
                (show ‖fwdDiff (coordinateStep second) hodgeReciprocal
                    (frequency + coordinateStep second)‖ ≤ firstBound by
                  simpa [firstBound] using hry1)
                (norm_nonneg _) (by positivity : 0 ≤ firstBound)
              have hmiddleTerm := mul_le_mul_of_nonneg_left hmiddleFactors
                (by norm_num : (0 : ℝ) ≤ 2)
              have hmiddleTerm' :
                  2 * ‖fwdDiff (coordinateStep second)
                        (fun current ↦ hodgeReciprocal
                          (current + coordinateStep first)) frequency‖ *
                      ‖fwdDiff (coordinateStep second) hodgeReciprocal
                        (frequency + coordinateStep second)‖ ≤
                    2 * firstBound * firstBound := by
                simpa only [mul_assoc] using hmiddleTerm
              have hlastTerm := mul_le_mul hr10
                (show ‖(fwdDiff (coordinateStep second))^[2]
                    hodgeReciprocal frequency‖ ≤ secondBound by
                  simpa [secondBound] using hryy0)
                (norm_nonneg _) (by positivity : 0 ≤ 1 / lower)
              exact add_le_add (add_le_add hfirstTerm hmiddleTerm') hlastTerm
      _ = 2 * (1 / lower) * secondBound + 2 * firstBound ^ 2 := by ring
  have h00Positive : 0 < frequencySquared frequency := hlower.trans_le h00
  have h10Positive : 0 < frequencySquared (frequency + coordinateStep first) :=
    hlower.trans_le h10
  have h01Positive : 0 < frequencySquared (frequency + coordinateStep second) :=
    hlower.trans_le h01
  have h11Positive :
      0 < frequencySquared (frequency + coordinateStep first + coordinateStep second) :=
    hlower.trans_le h11
  have h02Positive :
      0 < frequencySquared (frequency + coordinateStep second + coordinateStep second) :=
    hlower.trans_le h02
  have h12Positive : 0 < frequencySquared
      (frequency + coordinateStep first + coordinateStep second + coordinateStep second) :=
    hlower.trans_le h12
  have hdx0 := fwdDiff_hodgeReciprocal_eq first frequency
    h00Positive.ne' h10Positive.ne'
  have hdx1 := fwdDiff_hodgeReciprocal_eq first
    (frequency + coordinateStep second) h01Positive.ne' (by
      simpa [add_assoc, add_left_comm, add_comm] using h11Positive.ne')
  have hdx2 := fwdDiff_hodgeReciprocal_eq first
    (frequency + coordinateStep second + coordinateStep second) h02Positive.ne' (by
      simpa [add_assoc, add_left_comm, add_comm] using h12Positive.ne')
  rw [frequencySquared_change_add_distinct first second haxes frequency] at hdx1
  rw [frequencySquared_change_add_distinct first second haxes
      (frequency + coordinateStep second),
    frequencySquared_change_add_distinct first second haxes frequency] at hdx2
  have hcomm := congrFun
    (fwdDiff_iter_two_comm (coordinateStep first) (coordinateStep second)
      hodgeReciprocal) frequency
  have hidentity :
      mixedForwardDifference first second 1 2 hodgeReciprocal frequency =
        -((frequencySquared (frequency + coordinateStep first) -
            frequencySquared frequency : ℝ) : ℂ) *
          (fwdDiff (coordinateStep second))^[2]
            (fun current ↦ hodgeReciprocal (current + coordinateStep first) *
              hodgeReciprocal current) frequency := by
    unfold mixedForwardDifference
    simp only [Function.iterate_one]
    rw [hcomm]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
    rw [show
      hodgeReciprocal
            (frequency + coordinateStep second + coordinateStep second +
              coordinateStep first) -
          hodgeReciprocal (frequency + coordinateStep second + coordinateStep second) =
        fwdDiff (coordinateStep first) hodgeReciprocal
          (frequency + coordinateStep second + coordinateStep second) by rfl,
      show hodgeReciprocal (frequency + coordinateStep second + coordinateStep first) -
          hodgeReciprocal (frequency + coordinateStep second) =
        fwdDiff (coordinateStep first) hodgeReciprocal
          (frequency + coordinateStep second) by rfl,
      show hodgeReciprocal (frequency + coordinateStep first) -
          hodgeReciprocal frequency =
        fwdDiff (coordinateStep first) hodgeReciprocal frequency by rfl,
      hdx2, hdx1, hdx0]
    ring
  have hchange :
      |frequencySquared (frequency + coordinateStep first) -
          frequencySquared frequency| ≤ 2 * bound + 1 := by
    rw [add_coordinateStep_eq_increment]
    exact abs_frequencySquared_increment_sub_le hbound frequency hc00 first
  rw [hidentity, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  calc
    |frequencySquared (frequency + coordinateStep first) -
          frequencySquared frequency| *
        ‖(fwdDiff (coordinateStep second))^[2]
          (fun current ↦ hodgeReciprocal (current + coordinateStep first) *
            hodgeReciprocal current) frequency‖ ≤
      (2 * bound + 1) *
        (2 * (1 / lower) * secondBound + 2 * firstBound ^ 2) := by gcongr
    _ = (2 * bound + 1) *
        (2 * (1 / lower) *
            (2 / lower ^ 2 +
              ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
          2 * ((2 * bound + 1) / lower ^ 2) ^ 2) := by
            rfl

/-- Two-by-two distinct-axis reciprocal variation.  The first term is the transported quadratic
denominator residue; the second is the exact two-step span interaction of three reciprocals. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_two_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 2) :
    ‖mixedForwardDifference first second 2 2 hodgeReciprocal frequency‖ ≤
      2 *
          (2 * (1 / lower) *
              (2 / lower ^ 2 +
                ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
            2 * ((2 * bound + 1) / lower ^ 2) ^ 2) +
        (2 * bound + 1) * (4 * bound + 4) *
          (3 * (1 / lower) ^ 2 *
              (2 / lower ^ 2 +
                ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
            6 * (1 / lower) * ((2 * bound + 1) / lower ^ 2) ^ 2) := by
  let point := twoAxisStencilPoint first second frequency
  let reciprocal := hodgeReciprocal
  let firstBound := (2 * bound + 1) / lower ^ 2
  let secondBound := 2 / lower ^ 2 +
    ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3
  let pairSecondBound := 2 * (1 / lower) * secondBound + 2 * firstBound ^ 2
  let tripleSecondBound :=
    3 * (1 / lower) ^ 2 * secondBound +
      6 * (1 / lower) * firstBound ^ 2
  have hp00 : point 0 0 = frequency := by
    simp [point]
  have hp10 : point 1 0 = frequency + coordinateStep first := by
    simp [point, twoAxisStencilPoint]
  have hp20 : point 2 0 =
      frequency + coordinateStep first + coordinateStep first := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp01 : point 0 1 = frequency + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp11 : point 1 1 =
      frequency + coordinateStep first + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp21 : point 2 1 =
      frequency + coordinateStep first + coordinateStep first +
        coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp02 : point 0 2 =
      frequency + coordinateStep second + coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp12 : point 1 2 =
      frequency + coordinateStep first + coordinateStep second +
        coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp22 : point 2 2 =
      frequency + coordinateStep first + coordinateStep first +
        coordinateStep second + coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hvalue : ∀ i ≤ 2, ∀ j ≤ 2,
      ‖reciprocal (point i j)‖ ≤ 1 / lower := by
    intro i hi j hj
    exact norm_hodgeReciprocal_le hlower _ (hstencil i hi j hj).1
  have hfirstDifference : ∀ i ≤ 2, ∀ j ≤ 1,
      ‖fwdDiff (coordinateStep second) reciprocal (point i j)‖ ≤ firstBound := by
    intro i hi j hj
    have hnext : lower ≤
        frequencySquared (point i j + coordinateStep second) := by
      rw [← twoAxisStencilPoint_succ_second first second frequency i j]
      exact (hstencil i hi (j + 1) (by omega)).1
    simpa [firstBound, point, reciprocal] using
      norm_fwdDiff_hodgeReciprocal_le hlower hbound second (point i j)
        (hstencil i hi j (by omega)).2 (hstencil i hi j (by omega)).1 hnext
  have hsecondDifference : ∀ i ≤ 2,
      ‖(fwdDiff (coordinateStep second))^[2] reciprocal (point i 0)‖ ≤
        secondBound := by
    intro i hi
    have hmiddle : lower ≤
        frequencySquared (point i 0 + coordinateStep second) := by
      rw [← twoAxisStencilPoint_succ_second first second frequency i 0]
      exact (hstencil i hi 1 (by omega)).1
    have hlast : lower ≤ frequencySquared
        (point i 0 + coordinateStep second + coordinateStep second) := by
      rw [← twoAxisStencilPoint_succ_second first second frequency i 0,
        ← twoAxisStencilPoint_succ_second first second frequency i 1]
      exact (hstencil i hi 2 (by omega)).1
    simpa [secondBound, point, reciprocal] using
      norm_fwdDiff_iter_two_hodgeReciprocal_le hlower hbound second (point i 0)
        (hstencil i hi 0 (by omega)).2 (hstencil i hi 0 (by omega)).1
        hmiddle hlast
  let shiftedOne : SpatialFrequency → ℂ :=
    fun current ↦ reciprocal (current + coordinateStep first)
  let shiftedTwo : SpatialFrequency → ℂ :=
    fun current ↦ reciprocal
      (current + coordinateStep first + coordinateStep first)
  have hshiftedOneValue : ‖shiftedOne frequency‖ ≤ 1 / lower := by
    rw [show shiftedOne frequency = reciprocal (point 1 0) by
      simp [shiftedOne, hp10]]
    exact hvalue 1 (by omega) 0 (by omega)
  have hshiftedTwoValue : ‖shiftedTwo frequency‖ ≤ 1 / lower := by
    rw [show shiftedTwo frequency = reciprocal (point 2 0) by
      simp [shiftedTwo, hp20]]
    exact hvalue 2 (by omega) 0 (by omega)
  have hshiftedOneValueLast :
      ‖shiftedOne (frequency + coordinateStep second + coordinateStep second)‖ ≤
        1 / lower := by
    rw [show shiftedOne (frequency + coordinateStep second + coordinateStep second) =
        reciprocal (point 1 2) by
      simp [shiftedOne, hp12, add_left_comm, add_comm]]
    exact hvalue 1 (by omega) 2 (by omega)
  have hshiftedTwoValueLast :
      ‖shiftedTwo (frequency + coordinateStep second + coordinateStep second)‖ ≤
        1 / lower := by
    rw [show shiftedTwo (frequency + coordinateStep second + coordinateStep second) =
        reciprocal (point 2 2) by
      simp [shiftedTwo, hp22, add_left_comm, add_comm]]
    exact hvalue 2 (by omega) 2 (by omega)
  have hshiftedOneFirst :
      ‖fwdDiff (coordinateStep second) shiftedOne frequency‖ ≤ firstBound := by
    rw [show fwdDiff (coordinateStep second) shiftedOne frequency =
        fwdDiff (coordinateStep second) reciprocal (point 1 0) by
      rw [show shiftedOne =
          fun current ↦ reciprocal (current + coordinateStep first) by rfl,
        congrFun (fwdDiff_translate (coordinateStep second)
          (coordinateStep first) reciprocal) frequency, hp10]]
    exact hfirstDifference 1 (by omega) 0 (by omega)
  have hshiftedTwoFirst :
      ‖fwdDiff (coordinateStep second) shiftedTwo frequency‖ ≤ firstBound := by
    rw [show fwdDiff (coordinateStep second) shiftedTwo frequency =
        fwdDiff (coordinateStep second) reciprocal (point 2 0) by
      rw [show shiftedTwo = fun current ↦
          reciprocal (current + (coordinateStep first + coordinateStep first)) by
        funext current
        simp [shiftedTwo, add_assoc],
        congrFun (fwdDiff_translate (coordinateStep second)
          (coordinateStep first + coordinateStep first) reciprocal) frequency,
        hp20]
      simp only [add_assoc]]
    exact hfirstDifference 2 (by omega) 0 (by omega)
  have hshiftedOneFirstNext :
      ‖fwdDiff (coordinateStep second) shiftedOne
        (frequency + coordinateStep second)‖ ≤ firstBound := by
    rw [show fwdDiff (coordinateStep second) shiftedOne
          (frequency + coordinateStep second) =
        fwdDiff (coordinateStep second) reciprocal (point 1 1) by
      rw [show shiftedOne =
          fun current ↦ reciprocal (current + coordinateStep first) by rfl,
        congrFun (fwdDiff_translate (coordinateStep second)
          (coordinateStep first) reciprocal) (frequency + coordinateStep second),
        hp11]
      simp [add_left_comm, add_comm]]
    exact hfirstDifference 1 (by omega) 1 (by omega)
  have hshiftedTwoFirstNext :
      ‖fwdDiff (coordinateStep second) shiftedTwo
        (frequency + coordinateStep second)‖ ≤ firstBound := by
    rw [show fwdDiff (coordinateStep second) shiftedTwo
          (frequency + coordinateStep second) =
        fwdDiff (coordinateStep second) reciprocal (point 2 1) by
      rw [show shiftedTwo = fun current ↦
          reciprocal (current + (coordinateStep first + coordinateStep first)) by
        funext current
        simp [shiftedTwo, add_assoc],
        congrFun (fwdDiff_translate (coordinateStep second)
          (coordinateStep first + coordinateStep first) reciprocal)
          (frequency + coordinateStep second), hp21]
      simp [add_left_comm, add_comm]]
    exact hfirstDifference 2 (by omega) 1 (by omega)
  have hshiftedOneSecond :
      ‖(fwdDiff (coordinateStep second))^[2] shiftedOne frequency‖ ≤
        secondBound := by
    rw [show (fwdDiff (coordinateStep second))^[2] shiftedOne frequency =
        (fwdDiff (coordinateStep second))^[2] reciprocal (point 1 0) by
      rw [show shiftedOne =
          fun current ↦ reciprocal (current + coordinateStep first) by rfl,
        congrFun (fwdDiff_iter_two_translate (coordinateStep second)
          (coordinateStep first) reciprocal) frequency, hp10]]
    exact hsecondDifference 1 (by omega)
  have hshiftedTwoSecond :
      ‖(fwdDiff (coordinateStep second))^[2] shiftedTwo frequency‖ ≤
        secondBound := by
    rw [show (fwdDiff (coordinateStep second))^[2] shiftedTwo frequency =
        (fwdDiff (coordinateStep second))^[2] reciprocal (point 2 0) by
      rw [show shiftedTwo = fun current ↦
          reciprocal (current + (coordinateStep first + coordinateStep first)) by
        funext current
        simp [shiftedTwo, add_assoc],
        congrFun (fwdDiff_iter_two_translate (coordinateStep second)
          (coordinateStep first + coordinateStep first) reciprocal) frequency,
        hp20]
      simp only [add_assoc]]
    exact hsecondDifference 2 (by omega)
  let pair : SpatialFrequency → ℂ :=
    fun current ↦ shiftedTwo current * shiftedOne current
  have hpairSecond :
      ‖(fwdDiff (coordinateStep second))^[2] pair frequency‖ ≤
        pairSecondBound := by
    have hraw := norm_fwdDiff_iter_two_mul_le (coordinateStep second)
      shiftedTwo shiftedOne frequency
    refine hraw.trans ?_
    dsimp [pairSecondBound]
    calc
      ‖(fwdDiff (coordinateStep second))^[2] shiftedTwo frequency‖ *
            ‖shiftedOne
              (frequency + coordinateStep second + coordinateStep second)‖ +
          2 * ‖fwdDiff (coordinateStep second) shiftedTwo frequency‖ *
            ‖fwdDiff (coordinateStep second) shiftedOne
              (frequency + coordinateStep second)‖ +
          ‖shiftedTwo frequency‖ *
            ‖(fwdDiff (coordinateStep second))^[2] shiftedOne frequency‖ ≤
        secondBound * (1 / lower) +
          2 * firstBound * firstBound +
            (1 / lower) * secondBound := by
              have hfirstTerm := mul_le_mul hshiftedTwoSecond hshiftedOneValueLast
                (norm_nonneg _) (by positivity : 0 ≤ secondBound)
              have hmiddleFactors := mul_le_mul hshiftedTwoFirst
                hshiftedOneFirstNext (norm_nonneg _)
                (by positivity : 0 ≤ firstBound)
              have hmiddleTerm := mul_le_mul_of_nonneg_left hmiddleFactors
                (by norm_num : (0 : ℝ) ≤ 2)
              have hmiddleTerm' :
                  2 * ‖fwdDiff (coordinateStep second) shiftedTwo frequency‖ *
                      ‖fwdDiff (coordinateStep second) shiftedOne
                        (frequency + coordinateStep second)‖ ≤
                    2 * firstBound * firstBound := by
                simpa only [mul_assoc] using hmiddleTerm
              have hlastTerm := mul_le_mul hshiftedTwoValue hshiftedOneSecond
                (norm_nonneg _) (by positivity : 0 ≤ 1 / lower)
              exact add_le_add (add_le_add hfirstTerm hmiddleTerm') hlastTerm
      _ = 2 * (1 / lower) * secondBound + 2 * firstBound ^ 2 := by ring
  let basePair : SpatialFrequency → ℂ :=
    fun current ↦ reciprocal current * shiftedOne current
  have hbasePairValue : ‖basePair frequency‖ ≤ (1 / lower) ^ 2 := by
    dsimp [basePair]
    rw [norm_mul]
    calc
      ‖reciprocal frequency‖ * ‖shiftedOne frequency‖ ≤
          (1 / lower) * (1 / lower) := by
        exact mul_le_mul
          (show ‖reciprocal frequency‖ ≤ 1 / lower by
            rw [← hp00]
            exact hvalue 0 (by omega) 0 (by omega)) hshiftedOneValue
          (norm_nonneg _) (by positivity)
      _ = (1 / lower) ^ 2 := by ring
  have hbasePairFirst :
      ‖fwdDiff (coordinateStep second) basePair frequency‖ ≤
        2 * (1 / lower) * firstBound := by
    have hraw := norm_fwdDiff_mul_le (coordinateStep second)
      reciprocal shiftedOne frequency
    refine hraw.trans ?_
    calc
      ‖fwdDiff (coordinateStep second) reciprocal frequency‖ *
            ‖shiftedOne (frequency + coordinateStep second)‖ +
          ‖reciprocal frequency‖ *
            ‖fwdDiff (coordinateStep second) shiftedOne frequency‖ ≤
        firstBound * (1 / lower) + (1 / lower) * firstBound := by
          apply add_le_add
          · exact mul_le_mul
              (show ‖fwdDiff (coordinateStep second) reciprocal frequency‖ ≤
                  firstBound by
                rw [← hp00]
                exact hfirstDifference 0 (by omega) 0 (by omega))
              (show ‖shiftedOne (frequency + coordinateStep second)‖ ≤
                  1 / lower by
                rw [show shiftedOne (frequency + coordinateStep second) =
                    reciprocal (point 1 1) by
                  simp [shiftedOne, hp11, add_left_comm, add_comm]]
                exact hvalue 1 (by omega) 1 (by omega))
              (norm_nonneg _) (by positivity)
          · exact mul_le_mul
              (show ‖reciprocal frequency‖ ≤ 1 / lower by
                rw [← hp00]
                exact hvalue 0 (by omega) 0 (by omega))
              hshiftedOneFirst (norm_nonneg _) (by positivity)
      _ = 2 * (1 / lower) * firstBound := by ring
  have hbasePairSecond :
      ‖(fwdDiff (coordinateStep second))^[2] basePair frequency‖ ≤
        pairSecondBound := by
    have hraw := norm_fwdDiff_iter_two_mul_le (coordinateStep second)
      reciprocal shiftedOne frequency
    refine hraw.trans ?_
    dsimp [pairSecondBound]
    calc
      ‖(fwdDiff (coordinateStep second))^[2] reciprocal frequency‖ *
            ‖shiftedOne
              (frequency + coordinateStep second + coordinateStep second)‖ +
          2 * ‖fwdDiff (coordinateStep second) reciprocal frequency‖ *
            ‖fwdDiff (coordinateStep second) shiftedOne
              (frequency + coordinateStep second)‖ +
          ‖reciprocal frequency‖ *
            ‖(fwdDiff (coordinateStep second))^[2] shiftedOne frequency‖ ≤
        secondBound * (1 / lower) + 2 * firstBound * firstBound +
          (1 / lower) * secondBound := by
            have hfirstTerm := mul_le_mul
              (show ‖(fwdDiff (coordinateStep second))^[2] reciprocal frequency‖ ≤
                  secondBound by
                rw [← hp00]
                exact hsecondDifference 0 (by omega)) hshiftedOneValueLast
              (norm_nonneg _) (by positivity : 0 ≤ secondBound)
            have hmiddleFactors := mul_le_mul
              (show ‖fwdDiff (coordinateStep second) reciprocal frequency‖ ≤
                  firstBound by
                rw [← hp00]
                exact hfirstDifference 0 (by omega) 0 (by omega))
              hshiftedOneFirstNext
              (norm_nonneg _) (by positivity : 0 ≤ firstBound)
            have hmiddleTerm := mul_le_mul_of_nonneg_left hmiddleFactors
              (by norm_num : (0 : ℝ) ≤ 2)
            have hmiddleTerm' :
                2 * ‖fwdDiff (coordinateStep second) reciprocal frequency‖ *
                    ‖fwdDiff (coordinateStep second) shiftedOne
                      (frequency + coordinateStep second)‖ ≤
                  2 * firstBound * firstBound := by
              simpa only [mul_assoc] using hmiddleTerm
            have hlastTerm := mul_le_mul
              (show ‖reciprocal frequency‖ ≤ 1 / lower by
                rw [← hp00]
                exact hvalue 0 (by omega) 0 (by omega)) hshiftedOneSecond
              (norm_nonneg _) (by positivity : 0 ≤ 1 / lower)
            exact add_le_add (add_le_add hfirstTerm hmiddleTerm') hlastTerm
      _ = 2 * (1 / lower) * secondBound + 2 * firstBound ^ 2 := by ring
  let triple : SpatialFrequency → ℂ :=
    fun current ↦ basePair current * shiftedTwo current
  have htripleSecond :
      ‖(fwdDiff (coordinateStep second))^[2] triple frequency‖ ≤
        tripleSecondBound := by
    have hraw := norm_fwdDiff_iter_two_mul_le (coordinateStep second)
      basePair shiftedTwo frequency
    refine hraw.trans ?_
    dsimp [tripleSecondBound]
    calc
      ‖(fwdDiff (coordinateStep second))^[2] basePair frequency‖ *
            ‖shiftedTwo
              (frequency + coordinateStep second + coordinateStep second)‖ +
          2 * ‖fwdDiff (coordinateStep second) basePair frequency‖ *
            ‖fwdDiff (coordinateStep second) shiftedTwo
              (frequency + coordinateStep second)‖ +
          ‖basePair frequency‖ *
            ‖(fwdDiff (coordinateStep second))^[2] shiftedTwo frequency‖ ≤
        pairSecondBound * (1 / lower) +
          2 * (2 * (1 / lower) * firstBound) * firstBound +
            (1 / lower) ^ 2 * secondBound := by
              have hfirstTerm := mul_le_mul hbasePairSecond hshiftedTwoValueLast
                (norm_nonneg _) (by positivity : 0 ≤ pairSecondBound)
              have hmiddleFactors := mul_le_mul hbasePairFirst
                hshiftedTwoFirstNext (norm_nonneg _)
                (by positivity : 0 ≤ 2 * (1 / lower) * firstBound)
              have hmiddleTerm := mul_le_mul_of_nonneg_left hmiddleFactors
                (by norm_num : (0 : ℝ) ≤ 2)
              have hmiddleTerm' :
                  2 * ‖fwdDiff (coordinateStep second) basePair frequency‖ *
                      ‖fwdDiff (coordinateStep second) shiftedTwo
                        (frequency + coordinateStep second)‖ ≤
                    2 * (2 * (1 / lower) * firstBound) * firstBound := by
                simpa only [mul_assoc] using hmiddleTerm
              have hlastTerm := mul_le_mul hbasePairValue hshiftedTwoSecond
                (norm_nonneg _) (by positivity : 0 ≤ (1 / lower) ^ 2)
              exact add_le_add (add_le_add hfirstTerm hmiddleTerm') hlastTerm
      _ = 3 * (1 / lower) ^ 2 * secondBound +
          6 * (1 / lower) * firstBound ^ 2 := by
            dsimp [pairSecondBound]
            ring
  have hpositive : ∀ i ≤ 2, ∀ j ≤ 2,
      frequencySquared (point i j) ≠ 0 := by
    intro i hi j hj
    exact (hlower.trans_le (hstencil i hi j hj).1).ne'
  have hxx0 := fwdDiff_iter_two_hodgeReciprocal_eq first frequency
    (by simpa [← hp00] using hpositive 0 (by omega) 0 (by omega))
    (by simpa [← hp10] using hpositive 1 (by omega) 0 (by omega))
    (by simpa [← hp20] using hpositive 2 (by omega) 0 (by omega))
  have hxx1 := fwdDiff_iter_two_hodgeReciprocal_eq first
    (frequency + coordinateStep second)
    (by rw [← hp01]; exact hpositive 0 (by omega) 1 (by omega))
    (by
      rw [show frequency + coordinateStep second + coordinateStep first = point 1 1 by
        rw [hp11]
        abel]
      exact hpositive 1 (by omega) 1 (by omega))
    (by
      rw [show frequency + coordinateStep second + coordinateStep first +
          coordinateStep first = point 2 1 by
        rw [hp21]
        abel]
      exact hpositive 2 (by omega) 1 (by omega))
  have hxx2 := fwdDiff_iter_two_hodgeReciprocal_eq first
    (frequency + coordinateStep second + coordinateStep second)
    (by rw [← hp02]; exact hpositive 0 (by omega) 2 (by omega))
    (by
      rw [show frequency + coordinateStep second + coordinateStep second +
          coordinateStep first = point 1 2 by
        rw [hp12]
        abel]
      exact hpositive 1 (by omega) 2 (by omega))
    (by
      rw [show frequency + coordinateStep second + coordinateStep second +
          coordinateStep first + coordinateStep first = point 2 2 by
        rw [hp22]
        abel]
      exact hpositive 2 (by omega) 2 (by omega))
  rw [frequencySquared_change_add_distinct first second haxes frequency,
    frequencySquared_twoStepSpan_add_distinct first second haxes frequency] at hxx1
  rw [frequencySquared_change_add_distinct first second haxes
      (frequency + coordinateStep second),
    frequencySquared_change_add_distinct first second haxes frequency,
    frequencySquared_twoStepSpan_add_distinct first second haxes
      (frequency + coordinateStep second),
    frequencySquared_twoStepSpan_add_distinct first second haxes frequency] at hxx2
  have hcomm := congrFun
    (fwdDiff_iter_two_iter_two_comm (coordinateStep first) (coordinateStep second)
      reciprocal) frequency
  have hidentity :
      mixedForwardDifference first second 2 2 reciprocal frequency =
        -2 * (fwdDiff (coordinateStep second))^[2] pair frequency +
          ((frequencySquared (frequency + coordinateStep first) -
              frequencySquared frequency : ℝ) : ℂ) *
            ((frequencySquared
                (frequency + coordinateStep first + coordinateStep first) -
              frequencySquared frequency : ℝ) : ℂ) *
              (fwdDiff (coordinateStep second))^[2] triple frequency := by
    unfold mixedForwardDifference
    rw [hcomm]
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, fwdDiff]
    rw [show reciprocal
            (frequency + coordinateStep second + coordinateStep second +
              coordinateStep first + coordinateStep first) -
          reciprocal
            (frequency + coordinateStep second + coordinateStep second +
              coordinateStep first) -
          (reciprocal
              (frequency + coordinateStep second + coordinateStep second +
                coordinateStep first) -
            reciprocal
              (frequency + coordinateStep second + coordinateStep second)) =
        (fwdDiff (coordinateStep first))^[2] reciprocal
          (frequency + coordinateStep second + coordinateStep second) by rfl,
      show reciprocal
            (frequency + coordinateStep second + coordinateStep first +
              coordinateStep first) -
          reciprocal (frequency + coordinateStep second + coordinateStep first) -
          (reciprocal (frequency + coordinateStep second + coordinateStep first) -
            reciprocal (frequency + coordinateStep second)) =
        (fwdDiff (coordinateStep first))^[2] reciprocal
          (frequency + coordinateStep second) by rfl,
      show reciprocal (frequency + coordinateStep first + coordinateStep first) -
          reciprocal (frequency + coordinateStep first) -
          (reciprocal (frequency + coordinateStep first) - reciprocal frequency) =
        (fwdDiff (coordinateStep first))^[2] reciprocal frequency by rfl,
      hxx2, hxx1, hxx0]
    dsimp [pair, triple, basePair, shiftedOne, shiftedTwo, reciprocal]
    ring
  have hchange :
      |frequencySquared (frequency + coordinateStep first) -
          frequencySquared frequency| ≤ 2 * bound + 1 := by
    rw [add_coordinateStep_eq_increment]
    exact abs_frequencySquared_increment_sub_le hbound frequency
      (by simpa [point, hp00] using (hstencil 0 (by omega) 0 (by omega)).2) first
  have hspan :
      |frequencySquared (frequency + coordinateStep first + coordinateStep first) -
          frequencySquared frequency| ≤ 4 * bound + 4 :=
    abs_frequencySquared_add_two_coordinateStep_sub_le first frequency
      (by simpa [point, hp00] using (hstencil 0 (by omega) 0 (by omega)).2)
  rw [hidentity]
  calc
    ‖-2 * (fwdDiff (coordinateStep second))^[2] pair frequency +
          ((frequencySquared (frequency + coordinateStep first) -
              frequencySquared frequency : ℝ) : ℂ) *
            ((frequencySquared
                (frequency + coordinateStep first + coordinateStep first) -
              frequencySquared frequency : ℝ) : ℂ) *
              (fwdDiff (coordinateStep second))^[2] triple frequency‖ ≤
      2 * ‖(fwdDiff (coordinateStep second))^[2] pair frequency‖ +
        |frequencySquared (frequency + coordinateStep first) -
            frequencySquared frequency| *
          |frequencySquared
              (frequency + coordinateStep first + coordinateStep first) -
            frequencySquared frequency| *
          ‖(fwdDiff (coordinateStep second))^[2] triple frequency‖ := by
            calc
              _ ≤ ‖-2 * (fwdDiff (coordinateStep second))^[2] pair frequency‖ +
                  ‖((frequencySquared (frequency + coordinateStep first) -
                        frequencySquared frequency : ℝ) : ℂ) *
                    ((frequencySquared
                        (frequency + coordinateStep first + coordinateStep first) -
                      frequencySquared frequency : ℝ) : ℂ) *
                    (fwdDiff (coordinateStep second))^[2] triple frequency‖ :=
                norm_add_le _ _
              _ = _ := by
                simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
                rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    _ ≤ 2 * pairSecondBound +
        (2 * bound + 1) * (4 * bound + 4) * tripleSecondBound := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hpairSecond (by norm_num)
          · exact mul_le_mul
              (mul_le_mul hchange hspan (abs_nonneg _) (by positivity))
              htripleSecond (norm_nonneg _) (by positivity)
    _ = 2 *
          (2 * (1 / lower) *
              (2 / lower ^ 2 +
                ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
            2 * ((2 * bound + 1) / lower ^ 2) ^ 2) +
        (2 * bound + 1) * (4 * bound + 4) *
          (3 * (1 / lower) ^ 2 *
              (2 / lower ^ 2 +
                ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3) +
            6 * (1 / lower) * ((2 * bound + 1) / lower ^ 2) ^ 2) := by
              rfl

/-! ## Reusable reciprocal envelope chart -/

def hodgeReciprocalValueEnvelope (lower : ℝ) : ℝ := 1 / lower

def hodgeReciprocalFirstEnvelope (lower bound : ℝ) : ℝ :=
  (2 * bound + 1) / lower ^ 2

def hodgeReciprocalSecondEnvelope (lower bound : ℝ) : ℝ :=
  2 / lower ^ 2 +
    ((2 * bound + 1) * (4 * bound + 4)) / lower ^ 3

def hodgeReciprocalMixedOneOneEnvelope (lower bound : ℝ) : ℝ :=
  2 * (2 * bound + 1) ^ 2 / lower ^ 3

def hodgeReciprocalMixedOneTwoEnvelope (lower bound : ℝ) : ℝ :=
  (2 * bound + 1) *
    (2 * hodgeReciprocalValueEnvelope lower *
        hodgeReciprocalSecondEnvelope lower bound +
      2 * hodgeReciprocalFirstEnvelope lower bound ^ 2)

def hodgeReciprocalMixedTwoTwoEnvelope (lower bound : ℝ) : ℝ :=
  2 *
      (2 * hodgeReciprocalValueEnvelope lower *
          hodgeReciprocalSecondEnvelope lower bound +
        2 * hodgeReciprocalFirstEnvelope lower bound ^ 2) +
    (2 * bound + 1) * (4 * bound + 4) *
      (3 * hodgeReciprocalValueEnvelope lower ^ 2 *
          hodgeReciprocalSecondEnvelope lower bound +
        6 * hodgeReciprocalValueEnvelope lower *
          hodgeReciprocalFirstEnvelope lower bound ^ 2)

/-- Value envelope extracted directly from a controlled zero-order stencil. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_zero_zero_le
    {lower bound : ℝ} (hlower : 0 < lower)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 0 0) :
    ‖mixedForwardDifference first second 0 0 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalValueEnvelope lower := by
  unfold mixedForwardDifference
  simp only [Function.iterate_zero_apply]
  exact norm_hodgeReciprocal_le hlower frequency
    (by simpa using (hstencil 0 (by omega) 0 (by omega)).1)

/-- First envelope in the first displayed direction, read from an actual `2 × 1` stencil. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 0) :
    ‖mixedForwardDifference first second 1 0 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalFirstEnvelope lower bound := by
  have hcurrent : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by omega) 0 (by omega)).1
  have hnext : lower ≤ frequencySquared (frequency + coordinateStep first) := by
    simpa [twoAxisStencilPoint] using (hstencil 1 (by omega) 0 (by omega)).1
  unfold mixedForwardDifference
  simp only [Function.iterate_one, Function.iterate_zero_apply]
  simpa [hodgeReciprocalFirstEnvelope] using
    norm_fwdDiff_hodgeReciprocal_le hlower hbound first frequency
      (by simpa using (hstencil 0 (by omega) 0 (by omega)).2)
      hcurrent hnext

/-- Second envelope in the first displayed direction, read from an actual `3 × 1` stencil. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_two_zero_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 0) :
    ‖mixedForwardDifference first second 2 0 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalSecondEnvelope lower bound := by
  have hcurrent : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by omega) 0 (by omega)).1
  have hmiddle : lower ≤ frequencySquared (frequency + coordinateStep first) := by
    simpa [twoAxisStencilPoint] using (hstencil 1 (by omega) 0 (by omega)).1
  have hlast : lower ≤
      frequencySquared (frequency + coordinateStep first + coordinateStep first) := by
    rw [← show twoAxisStencilPoint first second frequency 2 0 =
        frequency + coordinateStep first + coordinateStep first by
      funext other
      simp [twoAxisStencilPoint]
      ring]
    exact (hstencil 2 (by omega) 0 (by omega)).1
  unfold mixedForwardDifference
  simp only [Function.iterate_zero_apply]
  simpa [hodgeReciprocalSecondEnvelope] using
    norm_fwdDiff_iter_two_hodgeReciprocal_le hlower hbound first frequency
      (by simpa using (hstencil 0 (by omega) 0 (by omega)).2)
      hcurrent hmiddle hlast

/-- First/first envelope read directly from a controlled four-corner stencil. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 1) :
    ‖mixedForwardDifference first second 1 1 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneOneEnvelope lower bound := by
  have h00 : lower ≤ frequencySquared frequency := by
    simpa using (hstencil 0 (by omega) 0 (by omega)).1
  have h10 : lower ≤ frequencySquared (frequency + coordinateStep first) := by
    simpa [twoAxisStencilPoint] using (hstencil 1 (by omega) 0 (by omega)).1
  have h01 : lower ≤ frequencySquared (frequency + coordinateStep second) := by
    simpa [twoAxisStencilPoint] using (hstencil 0 (by omega) 1 (by omega)).1
  have h11 : lower ≤
      frequencySquared (frequency + coordinateStep first + coordinateStep second) := by
    simpa [twoAxisStencilPoint] using (hstencil 1 (by omega) 1 (by omega)).1
  simpa [hodgeReciprocalMixedOneOneEnvelope] using
    norm_hodgeReciprocal_mixedForwardDifference_one_one_le hlower hbound
      first second haxes frequency
      (by simpa using (hstencil 0 (by omega) 0 (by omega)).2)
      (by simpa [twoAxisStencilPoint] using
        (hstencil 0 (by omega) 1 (by omega)).2)
      h00 h10 h01 h11

/-- The one/two envelope in its compact reusable chart. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_one_two_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 2) :
    ‖mixedForwardDifference first second 1 2 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneTwoEnvelope lower bound := by
  simpa [hodgeReciprocalMixedOneTwoEnvelope, hodgeReciprocalValueEnvelope,
    hodgeReciprocalFirstEnvelope, hodgeReciprocalSecondEnvelope] using
      norm_hodgeReciprocal_mixedForwardDifference_one_two_le
        hlower hbound first second haxes frequency hstencil

/-- Transposed two/one envelope; commutation preserves the same actual stencil population. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_two_one_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 1) :
    ‖mixedForwardDifference first second 2 1 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedOneTwoEnvelope lower bound := by
  have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_two_le_of_controlled
    hlower hbound second first haxes.symm frequency hstencil.transpose
  have hcomm := congrFun
    (fwdDiff_iter_two_comm (coordinateStep second) (coordinateStep first)
      hodgeReciprocal) frequency
  unfold mixedForwardDifference at hraw ⊢
  simp only [Function.iterate_one]
  rw [← hcomm]
  exact hraw

/-- Compact two/two envelope for the actual controlled `3 × 3` reciprocal stencil. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_two_two_le_of_controlled
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 2) :
    ‖mixedForwardDifference first second 2 2 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
  simpa [hodgeReciprocalMixedTwoTwoEnvelope, hodgeReciprocalValueEnvelope,
    hodgeReciprocalFirstEnvelope, hodgeReciprocalSecondEnvelope] using
      norm_hodgeReciprocal_mixedForwardDifference_two_two_le
        hlower hbound first second haxes frequency hstencil

/-- First envelope in the second displayed direction. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_zero_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 0 1) :
    ‖mixedForwardDifference first second 0 1 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalFirstEnvelope lower bound := by
  have hraw := norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
    hlower hbound second first frequency hstencil.transpose
  unfold mixedForwardDifference at hraw ⊢
  simp only [Function.iterate_zero_apply, Function.iterate_one]
  exact hraw

/-- Second envelope in the second displayed direction. -/
theorem norm_hodgeReciprocal_mixedForwardDifference_zero_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 0 2) :
    ‖mixedForwardDifference first second 0 2 hodgeReciprocal frequency‖ ≤
      hodgeReciprocalSecondEnvelope lower bound := by
  have hraw := norm_hodgeReciprocal_mixedForwardDifference_two_zero_le
    hlower hbound second first frequency hstencil.transpose
  unfold mixedForwardDifference at hraw ⊢
  simp only [Function.iterate_zero_apply]
  exact hraw

/-! ## Completed quadratic-numerator chart -/

/-- The transposed total-order-three numerator difference also vanishes. -/
theorem hodgeJacobianRatioNumerator_mixedForwardDifference_two_one_eq_zero
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    mixedForwardDifference first second 2 1
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency = 0 := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  have hzero :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
      second first frequency component coordinate input
  have hcomm := congrFun
    (fwdDiff_iter_two_comm (coordinateStep second) (coordinateStep first)
      numerator) frequency
  unfold mixedForwardDifference at hzero ⊢
  simp only [Function.iterate_one]
  rw [← hcomm]
  exact hzero

/-- Every total-order-four numerator difference vanishes. -/
theorem hodgeJacobianRatioNumerator_mixedForwardDifference_two_two_eq_zero
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    mixedForwardDifference first second 2 2
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency = 0 := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  have hzero : fwdDiff (coordinateStep first)
      ((fwdDiff (coordinateStep second))^[2] numerator) = 0 := by
    funext current
    exact hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
      first second current component coordinate input
  have houter := congrArg (fwdDiff (coordinateStep first)) hzero
  have hpoint := congrFun houter frequency
  unfold mixedForwardDifference
  simpa [numerator, Function.iterate_succ_apply', Function.iterate_zero_apply,
    fwdDiff] using hpoint

/-- First numerator variation in the first displayed axis. -/
theorem norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 1 0
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency‖ ≤ 2 * bound + 1 := by
  unfold mixedForwardDifference
  simp only [Function.iterate_one, Function.iterate_zero_apply, fwdDiff]
  rw [add_coordinateStep_eq_increment]
  exact norm_hodgeJacobianRatioNumerator_increment_sub_le hbound frequency
    hfrequency first component coordinate input

/-- First numerator variation in the second displayed axis. -/
theorem norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
    {bound : ℝ} (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (hfrequency : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 0 1
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency‖ ≤ 2 * bound + 1 := by
  unfold mixedForwardDifference
  simp only [Function.iterate_one, Function.iterate_zero_apply, fwdDiff]
  rw [add_coordinateStep_eq_increment]
  exact norm_hodgeJacobianRatioNumerator_increment_sub_le hbound frequency
    hfrequency second component coordinate input

/-- Same-axis numerator curvature in the first displayed direction. -/
theorem norm_hodgeJacobianRatioNumerator_mixedForwardDifference_two_zero_le_two
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 2 0
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency‖ ≤ 2 := by
  unfold mixedForwardDifference
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply',
    fwdDiff]
  rw [show
      hodgeJacobianRatioNumerator
            (frequency + coordinateStep first + coordinateStep first)
            component coordinate input -
          hodgeJacobianRatioNumerator (frequency + coordinateStep first)
            component coordinate input -
        (hodgeJacobianRatioNumerator (frequency + coordinateStep first)
            component coordinate input -
          hodgeJacobianRatioNumerator frequency component coordinate input) =
      hodgeJacobianRatioNumerator
            (frequency + coordinateStep first + coordinateStep first)
            component coordinate input -
        2 * hodgeJacobianRatioNumerator (frequency + coordinateStep first)
            component coordinate input +
          hodgeJacobianRatioNumerator frequency component coordinate input by ring,
    add_coordinateStep_eq_increment, add_coordinateStep_eq_increment]
  exact norm_hodgeJacobianRatioNumerator_secondDifference_le_two
    first frequency component coordinate input

/-- Same-axis numerator curvature in the second displayed direction. -/
theorem norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_two_le_two
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 0 2
      (fun current ↦ hodgeJacobianRatioNumerator current
        component coordinate input) frequency‖ ≤ 2 := by
  unfold mixedForwardDifference
  simp only [Function.iterate_zero_apply, Function.iterate_succ_apply',
    fwdDiff]
  rw [show
      hodgeJacobianRatioNumerator
            (frequency + coordinateStep second + coordinateStep second)
            component coordinate input -
          hodgeJacobianRatioNumerator (frequency + coordinateStep second)
            component coordinate input -
        (hodgeJacobianRatioNumerator (frequency + coordinateStep second)
            component coordinate input -
          hodgeJacobianRatioNumerator frequency component coordinate input) =
      hodgeJacobianRatioNumerator
            (frequency + coordinateStep second + coordinateStep second)
            component coordinate input -
        2 * hodgeJacobianRatioNumerator (frequency + coordinateStep second)
            component coordinate input +
          hodgeJacobianRatioNumerator frequency component coordinate input by ring,
    add_coordinateStep_eq_increment, add_coordinateStep_eq_increment]
  exact norm_hodgeJacobianRatioNumerator_secondDifference_le_two
    second frequency component coordinate input

/-! ## Actual rational Hodge entry -/

/-- Explicit order-four envelope for one genuine Hodge multiplier entry. -/
def hodgeJacobianEntryMixedTwoTwoEnvelope (lower bound : ℝ) : ℝ :=
  4 * hodgeReciprocalSecondEnvelope lower bound +
    8 * hodgeReciprocalMixedOneOneEnvelope lower bound +
    4 * (2 * bound + 1) * hodgeReciprocalMixedOneTwoEnvelope lower bound +
    3 * bound ^ 2 * hodgeReciprocalMixedTwoTwoEnvelope lower bound

/-- **Actual rational order-four estimate.** On every genuine controlled `3 × 3` frequency
stencil, the distinct-axis `Δ²×Δ²` variation of one Hodge entry has the explicit envelope
obtained from quadratic numerator cancellation and the derived reciprocal identities.  No
multiplier variation is accepted as a premise. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 2) :
    ‖mixedForwardDifference first second 2 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryMixedTwoTwoEnvelope lower bound := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  let reciprocal := hodgeReciprocal
  let point := twoAxisStencilPoint first second frequency
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeReciprocal,
      hodgeJacobianRatioNumerator, hodgeCrossBasisFactor, div_eq_mul_inv]
  have hp10 : point 1 0 = frequency + coordinateStep first := by
    simp [point, twoAxisStencilPoint]
  have hp20 : point 2 0 =
      frequency + coordinateStep first + coordinateStep first := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp01 : point 0 1 = frequency + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp11 : point 1 1 =
      frequency + coordinateStep first + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp02 : point 0 2 =
      frequency + coordinateStep second + coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hcontrol02 :
      TwoAxisStencilControlled lower bound first second (point 0 2) 2 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol11 :
      TwoAxisStencilControlled lower bound first second (point 1 1) 1 1 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol01 :
      TwoAxisStencilControlled lower bound first second (point 0 1) 2 1 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol20 :
      TwoAxisStencilControlled lower bound first second (point 2 0) 0 2 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol10 :
      TwoAxisStencilControlled lower bound first second (point 1 0) 1 2 :=
    hstencil.rebase (by omega) (by omega)
  have hreciprocal20 :
      ‖mixedForwardDifference first second 2 0 reciprocal
        (frequency + coordinateStep second + coordinateStep second)‖ ≤
        hodgeReciprocalSecondEnvelope lower bound := by
    rw [← hp02]
    exact norm_hodgeReciprocal_mixedForwardDifference_two_zero_le
      hlower hbound first second (point 0 2) hcontrol02
  have hreciprocal11 :
      ‖mixedForwardDifference first second 1 1 reciprocal
        (frequency + coordinateStep first + coordinateStep second)‖ ≤
        hodgeReciprocalMixedOneOneEnvelope lower bound := by
    rw [← hp11]
    exact norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound first second haxes (point 1 1) hcontrol11
  have hreciprocal21 :
      ‖mixedForwardDifference first second 2 1 reciprocal
        (frequency + coordinateStep second)‖ ≤
        hodgeReciprocalMixedOneTwoEnvelope lower bound := by
    rw [← hp01]
    exact norm_hodgeReciprocal_mixedForwardDifference_two_one_le_of_controlled
      hlower hbound first second haxes (point 0 1) hcontrol01
  have hreciprocal02 :
      ‖mixedForwardDifference first second 0 2 reciprocal
        (frequency + coordinateStep first + coordinateStep first)‖ ≤
        hodgeReciprocalSecondEnvelope lower bound := by
    rw [← hp20]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_two_le
      hlower hbound first second (point 2 0) hcontrol20
  have hreciprocal12 :
      ‖mixedForwardDifference first second 1 2 reciprocal
        (frequency + coordinateStep first)‖ ≤
        hodgeReciprocalMixedOneTwoEnvelope lower bound := by
    rw [← hp10]
    exact norm_hodgeReciprocal_mixedForwardDifference_one_two_le_of_controlled
      hlower hbound first second haxes (point 1 0) hcontrol10
  have hreciprocal22 :
      ‖mixedForwardDifference first second 2 2 reciprocal frequency‖ ≤
        hodgeReciprocalMixedTwoTwoEnvelope lower bound :=
    norm_hodgeReciprocal_mixedForwardDifference_two_two_le_of_controlled
      hlower hbound first second haxes frequency hstencil
  have hcoordinates : ∀ other : Fin 3,
      ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using
      (hstencil 0 (by omega) 0 (by omega)).2
  have hnumerator02 :
      ‖mixedForwardDifference first second 0 2 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_two_le_two
      first second frequency component coordinate input
  have hnumerator11 :
      ‖mixedForwardDifference first second 1 1 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
      first second frequency component coordinate input
  have hnumerator01 :
      ‖mixedForwardDifference first second 0 1 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator20 :
      ‖mixedForwardDifference first second 2 0 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_two_zero_le_two
      first second frequency component coordinate input
  have hnumerator10 :
      ‖mixedForwardDifference first second 1 0 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator00 : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hnumerator12 :
      mixedForwardDifference first second 1 2 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
      first second frequency component coordinate input
  have hnumerator21 :
      mixedForwardDifference first second 2 1 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_two_one_eq_zero
      first second frequency component coordinate input
  have hnumerator22 :
      mixedForwardDifference first second 2 2 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_two_two_eq_zero
      first second frequency component coordinate input
  let a := mixedForwardDifference first second 2 2 numerator frequency *
    reciprocal (frequency + coordinateStep second + coordinateStep second +
      coordinateStep first + coordinateStep first)
  let b := 2 * mixedForwardDifference first second 1 2 numerator frequency *
    mixedForwardDifference first second 1 0 reciprocal
      (frequency + coordinateStep second + coordinateStep second +
        coordinateStep first)
  let c := mixedForwardDifference first second 0 2 numerator frequency *
    mixedForwardDifference first second 2 0 reciprocal
      (frequency + coordinateStep second + coordinateStep second)
  let d := 2 * mixedForwardDifference first second 2 1 numerator frequency *
    mixedForwardDifference first second 0 1 reciprocal
      (frequency + coordinateStep first + coordinateStep first +
        coordinateStep second)
  let e := 4 * mixedForwardDifference first second 1 1 numerator frequency *
    mixedForwardDifference first second 1 1 reciprocal
      (frequency + coordinateStep first + coordinateStep second)
  let f := 2 * mixedForwardDifference first second 0 1 numerator frequency *
    mixedForwardDifference first second 2 1 reciprocal
      (frequency + coordinateStep second)
  let g := mixedForwardDifference first second 2 0 numerator frequency *
    mixedForwardDifference first second 0 2 reciprocal
      (frequency + coordinateStep first + coordinateStep first)
  let h := 2 * mixedForwardDifference first second 1 0 numerator frequency *
    mixedForwardDifference first second 1 2 reciprocal
      (frequency + coordinateStep first)
  let i := numerator frequency *
    mixedForwardDifference first second 2 2 reciprocal frequency
  have ha : ‖a‖ ≤ 0 := by simp [a, hnumerator22]
  have hb : ‖b‖ ≤ 0 := by simp [b, hnumerator12]
  have hc : ‖c‖ ≤ 2 * hodgeReciprocalSecondEnvelope lower bound := by
    dsimp [c]
    rw [norm_mul]
    exact mul_le_mul hnumerator02 hreciprocal20 (norm_nonneg _) (by positivity)
  have hd : ‖d‖ ≤ 0 := by simp [d, hnumerator21]
  have he : ‖e‖ ≤ 8 * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [e]
    rw [norm_mul, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    have hproduct := mul_le_mul hnumerator11 hreciprocal11
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
    nlinarith [norm_nonneg
      (mixedForwardDifference first second 1 1 numerator frequency),
      norm_nonneg (mixedForwardDifference first second 1 1 reciprocal
        (frequency + coordinateStep first + coordinateStep second))]
  have hf : ‖f‖ ≤
      2 * (2 * bound + 1) *
        hodgeReciprocalMixedOneTwoEnvelope lower bound := by
    dsimp [f]
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hproduct := mul_le_mul hnumerator01 hreciprocal21
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * bound + 1)
    nlinarith [norm_nonneg
      (mixedForwardDifference first second 0 1 numerator frequency),
      norm_nonneg (mixedForwardDifference first second 2 1 reciprocal
        (frequency + coordinateStep second))]
  have hg : ‖g‖ ≤ 2 * hodgeReciprocalSecondEnvelope lower bound := by
    dsimp [g]
    rw [norm_mul]
    exact mul_le_mul hnumerator20 hreciprocal02 (norm_nonneg _) (by positivity)
  have hh : ‖h‖ ≤
      2 * (2 * bound + 1) *
        hodgeReciprocalMixedOneTwoEnvelope lower bound := by
    dsimp [h]
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hproduct := mul_le_mul hnumerator10 hreciprocal12
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * bound + 1)
    nlinarith [norm_nonneg
      (mixedForwardDifference first second 1 0 numerator frequency),
      norm_nonneg (mixedForwardDifference first second 1 2 reciprocal
        (frequency + coordinateStep first))]
  have hi : ‖i‖ ≤
      3 * bound ^ 2 * hodgeReciprocalMixedTwoTwoEnvelope lower bound := by
    dsimp [i]
    rw [norm_mul]
    exact mul_le_mul hnumerator00 hreciprocal22 (norm_nonneg _) (by positivity)
  rw [hentry, mixedForwardDifference_two_two_mul_eq]
  change ‖a + b + c + d + e + f + g + h + i‖ ≤ _
  rw [show a + b + c + d + e + f + g + h + i =
      a + (b + (c + (d + (e + (f + (g + (h + i))))))) by ring]
  refine (norm_add_nine_le a b c d e f g h i).trans ?_
  let mass :=
    0 + (0 +
      (2 * hodgeReciprocalSecondEnvelope lower bound +
        (0 +
          (8 * hodgeReciprocalMixedOneOneEnvelope lower bound +
            (2 * (2 * bound + 1) *
                hodgeReciprocalMixedOneTwoEnvelope lower bound +
              (2 * hodgeReciprocalSecondEnvelope lower bound +
                (2 * (2 * bound + 1) *
                    hodgeReciprocalMixedOneTwoEnvelope lower bound +
                  3 * bound ^ 2 *
                    hodgeReciprocalMixedTwoTwoEnvelope lower bound)))))))
  have hmass :
      ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + (‖g‖ + (‖h‖ + ‖i‖))))))) ≤
        mass :=
    add_le_add ha (add_le_add hb
      (add_le_add hc (add_le_add hd
        (add_le_add he (add_le_add hf
          (add_le_add hg (add_le_add hh hi)))))))
  calc
    ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + (‖f‖ + (‖g‖ + (‖h‖ + ‖i‖))))))) ≤
      mass := hmass
    _ = hodgeJacobianEntryMixedTwoTwoEnvelope lower bound := by
      dsimp [mass, hodgeJacobianEntryMixedTwoTwoEnvelope]
      ring

section Audit

#print axioms norm_hodgeReciprocal_mixedForwardDifference_two_two_le
#print axioms norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_two_le

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
