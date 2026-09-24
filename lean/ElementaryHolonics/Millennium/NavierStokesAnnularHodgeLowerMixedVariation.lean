import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

/-!
# Lower mixed variations of the rational Hodge entry

**[proved-derived]** The order-four Hodge estimate is useful in a product rule only together with
all complementary lower orders.  This owner derives those genuine rational estimates from the
same controlled stencil, numerator, and reciprocal identities.  No multiplier-difference bound is
accepted as a premise.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeKernelDifference
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeLocalizedVariation
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation

/-! ## Missing discrete Leibniz faces -/

theorem fwdDiff_mul_eq
    (step : SpatialFrequency) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    fwdDiff step (fun current ↦ left current * right current) frequency =
      fwdDiff step left frequency * right (frequency + step) +
        left frequency * fwdDiff step right frequency := by
  simp only [fwdDiff]
  ring

theorem mixedForwardDifference_one_one_mul_eq
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 1 1
        (fun current ↦ left current * right current) frequency =
      mixedForwardDifference first second 1 1 left frequency *
          right (frequency + coordinateStep second + coordinateStep first) +
        mixedForwardDifference first second 0 1 left frequency *
          mixedForwardDifference first second 1 0 right
            (frequency + coordinateStep second) +
        mixedForwardDifference first second 1 0 left frequency *
          mixedForwardDifference first second 0 1 right
            (frequency + coordinateStep first) +
        left frequency *
          mixedForwardDifference first second 1 1 right frequency := by
  unfold mixedForwardDifference
  simp only [Function.iterate_one, Function.iterate_zero_apply, fwdDiff]
  simp only [add_assoc, add_comm, add_left_comm]
  ring

theorem mixedForwardDifference_one_two_mul_eq
    (first second : Fin 3) (left right : SpatialFrequency → ℂ)
    (frequency : SpatialFrequency) :
    mixedForwardDifference first second 1 2
        (fun current ↦ left current * right current) frequency =
      mixedForwardDifference first second 1 2 left frequency *
          right (frequency + coordinateStep second + coordinateStep second +
            coordinateStep first) +
        2 * mixedForwardDifference first second 1 1 left frequency *
          mixedForwardDifference first second 0 1 right
            (frequency + coordinateStep second + coordinateStep first) +
        mixedForwardDifference first second 1 0 left frequency *
          mixedForwardDifference first second 0 2 right
            (frequency + coordinateStep first) +
        mixedForwardDifference first second 0 2 left frequency *
          mixedForwardDifference first second 1 0 right
            (frequency + coordinateStep second + coordinateStep second) +
        2 * mixedForwardDifference first second 0 1 left frequency *
          mixedForwardDifference first second 1 1 right
            (frequency + coordinateStep second) +
        left frequency *
          mixedForwardDifference first second 1 2 right frequency := by
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
  simp only [Function.iterate_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change
    fwdDiff firstStep
        (fun current ↦ (fwdDiff secondStep)^[2] left current *
          right (current + secondStep + secondStep)) frequency +
      2 * fwdDiff firstStep
        (fun current ↦ fwdDiff secondStep left current *
          fwdDiff secondStep right (current + secondStep)) frequency +
      fwdDiff firstStep
        (fun current ↦ left current *
          (fwdDiff secondStep)^[2] right current) frequency = _
  rw [fwdDiff_mul_eq firstStep ((fwdDiff secondStep)^[2] left)
      (fun current ↦ right (current + secondStep + secondStep)) frequency,
    fwdDiff_mul_eq firstStep (fwdDiff secondStep left)
      (fun current ↦ fwdDiff secondStep right (current + secondStep)) frequency,
    fwdDiff_mul_eq firstStep left ((fwdDiff secondStep)^[2] right) frequency]
  rw [show (fun current ↦ right (current + secondStep + secondStep)) =
      fun current ↦ right (current + (secondStep + secondStep)) by
        funext current
        rw [add_assoc],
    congrFun (fwdDiff_translate firstStep (secondStep + secondStep) right) frequency,
    congrFun (fwdDiff_translate firstStep secondStep
      (fwdDiff secondStep right)) frequency]
  dsimp [firstStep, secondStep]
  simp only [add_assoc, add_comm, add_left_comm]
  ring

/-! ## Explicit entry envelopes -/

def hodgeJacobianEntryFirstEnvelope (lower bound : ℝ) : ℝ :=
  (2 * bound + 1) * hodgeReciprocalValueEnvelope lower +
    3 * bound ^ 2 * hodgeReciprocalFirstEnvelope lower bound

def hodgeJacobianEntrySecondEnvelope (lower bound : ℝ) : ℝ :=
  2 * hodgeReciprocalValueEnvelope lower +
    2 * (2 * bound + 1) * hodgeReciprocalFirstEnvelope lower bound +
    3 * bound ^ 2 * hodgeReciprocalSecondEnvelope lower bound

def hodgeJacobianEntryMixedOneOneEnvelope (lower bound : ℝ) : ℝ :=
  2 * hodgeReciprocalValueEnvelope lower +
    2 * (2 * bound + 1) * hodgeReciprocalFirstEnvelope lower bound +
    3 * bound ^ 2 * hodgeReciprocalMixedOneOneEnvelope lower bound

def hodgeJacobianEntryMixedOneTwoEnvelope (lower bound : ℝ) : ℝ :=
  6 * hodgeReciprocalFirstEnvelope lower bound +
    (2 * bound + 1) * hodgeReciprocalSecondEnvelope lower bound +
    2 * (2 * bound + 1) * hodgeReciprocalMixedOneOneEnvelope lower bound +
    3 * bound ^ 2 * hodgeReciprocalMixedOneTwoEnvelope lower bound

/-! ## Genuine controlled-stencil estimates -/

/-- First variation of one genuine Hodge entry. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_zero_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 0) :
    ‖mixedForwardDifference first second 1 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryFirstEnvelope lower bound := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  let reciprocal := hodgeReciprocal
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeReciprocal,
      hodgeJacobianRatioNumerator, hodgeCrossBasisFactor, div_eq_mul_inv]
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using
      (hstencil 0 (by omega) 0 (by omega)).2
  have hnumerator : ‖fwdDiff (coordinateStep first) numerator frequency‖ ≤
      2 * bound + 1 := by
    simpa [mixedForwardDifference] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
        hbound first second frequency hcoordinates component coordinate input
  have hnumeratorValue : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hreciprocalNext :
      ‖reciprocal (frequency + coordinateStep first)‖ ≤
        hodgeReciprocalValueEnvelope lower := by
    have hnextStencil : TwoAxisStencilControlled lower bound first second
        (twoAxisStencilPoint first second frequency 1 0) 0 0 :=
      hstencil.rebase (by omega) (by omega)
    have hpoint : twoAxisStencilPoint first second frequency 1 0 =
        frequency + coordinateStep first := by
      simp [twoAxisStencilPoint]
    rw [← hpoint]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_zero_le
      hlower first second (twoAxisStencilPoint first second frequency 1 0)
        hnextStencil
  have hreciprocalFirst :
      ‖fwdDiff (coordinateStep first) reciprocal frequency‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    simpa [mixedForwardDifference] using
      norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
        hlower hbound first second frequency hstencil
  rw [hentry]
  unfold mixedForwardDifference
  simp only [Function.iterate_one, Function.iterate_zero_apply]
  refine (norm_fwdDiff_mul_le (coordinateStep first) numerator reciprocal frequency).trans ?_
  dsimp [hodgeJacobianEntryFirstEnvelope]
  exact add_le_add
    (mul_le_mul hnumerator hreciprocalNext (norm_nonneg _) (by positivity))
    (mul_le_mul hnumeratorValue hreciprocalFirst (norm_nonneg _) (by positivity))

/-- Same-axis second variation of one genuine Hodge entry. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 0) :
    ‖mixedForwardDifference first second 2 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntrySecondEnvelope lower bound := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  let reciprocal := hodgeReciprocal
  let point := twoAxisStencilPoint first second frequency
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
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
  have hcontrol10 :
      TwoAxisStencilControlled lower bound first second (point 1 0) 1 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol20 :
      TwoAxisStencilControlled lower bound first second (point 2 0) 0 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using
      (hstencil 0 (by omega) 0 (by omega)).2
  have hnumeratorTwo :
      ‖(fwdDiff (coordinateStep first))^[2] numerator frequency‖ ≤ 2 := by
    simpa [mixedForwardDifference] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_two_zero_le_two
        first second frequency component coordinate input
  have hnumeratorFirst : ‖fwdDiff (coordinateStep first) numerator frequency‖ ≤
      2 * bound + 1 := by
    simpa [mixedForwardDifference] using
      norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
        hbound first second frequency hcoordinates component coordinate input
  have hnumeratorValue : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hreciprocalNext :
      ‖reciprocal (frequency + coordinateStep first + coordinateStep first)‖ ≤
        hodgeReciprocalValueEnvelope lower := by
    rw [← hp20]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_zero_le
      hlower first second (point 2 0) hcontrol20
  have hreciprocalFirst :
      ‖fwdDiff (coordinateStep first) reciprocal
          (frequency + coordinateStep first)‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    rw [← hp10]
    simpa [mixedForwardDifference] using
      norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
        hlower hbound first second (point 1 0) hcontrol10
  have hreciprocalTwo :
      ‖(fwdDiff (coordinateStep first))^[2] reciprocal frequency‖ ≤
        hodgeReciprocalSecondEnvelope lower bound := by
    simpa [mixedForwardDifference] using
      norm_hodgeReciprocal_mixedForwardDifference_two_zero_le
        hlower hbound first second frequency hstencil
  rw [hentry]
  unfold mixedForwardDifference
  simp only [Function.iterate_zero_apply]
  refine (norm_fwdDiff_iter_two_mul_le
    (coordinateStep first) numerator reciprocal frequency).trans ?_
  dsimp [hodgeJacobianEntrySecondEnvelope]
  have hfirst := mul_le_mul hnumeratorTwo hreciprocalNext
    (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
  have hmiddle := mul_le_mul hnumeratorFirst hreciprocalFirst
    (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * bound + 1)
  have hlast := mul_le_mul hnumeratorValue hreciprocalTwo
    (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 3 * bound ^ 2)
  have hmiddle' := mul_le_mul_of_nonneg_left hmiddle (by norm_num : (0 : ℝ) ≤ 2)
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply, mul_assoc,
    add_assoc] using
    add_le_add hfirst (add_le_add hmiddle' hlast)

/-- Distinct-axis first/first variation of one genuine Hodge entry. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 1) :
    ‖mixedForwardDifference first second 1 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryMixedOneOneEnvelope lower bound := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  let reciprocal := hodgeReciprocal
  let point := twoAxisStencilPoint first second frequency
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeReciprocal,
      hodgeJacobianRatioNumerator, hodgeCrossBasisFactor, div_eq_mul_inv]
  have hp01 : point 0 1 = frequency + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp10 : point 1 0 = frequency + coordinateStep first := by
    simp [point, twoAxisStencilPoint]
  have hp11 : point 1 1 =
      frequency + coordinateStep second + coordinateStep first := by
    unfold point twoAxisStencilPoint
    abel
  have hcontrol01 :
      TwoAxisStencilControlled lower bound first second (point 0 1) 1 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol10 :
      TwoAxisStencilControlled lower bound first second (point 1 0) 0 1 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol11 :
      TwoAxisStencilControlled lower bound first second (point 1 1) 0 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using
      (hstencil 0 (by omega) 0 (by omega)).2
  have hnumerator11 :
      ‖mixedForwardDifference first second 1 1 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
      first second frequency component coordinate input
  have hnumerator01 :
      ‖mixedForwardDifference first second 0 1 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator10 :
      ‖mixedForwardDifference first second 1 0 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator00 : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hreciprocal00 :
      ‖reciprocal (frequency + coordinateStep second + coordinateStep first)‖ ≤
        hodgeReciprocalValueEnvelope lower := by
    rw [← hp11]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_zero_le
      hlower first second (point 1 1) hcontrol11
  have hreciprocal10 :
      ‖mixedForwardDifference first second 1 0 reciprocal
          (frequency + coordinateStep second)‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    rw [← hp01]
    exact norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
      hlower hbound first second (point 0 1) hcontrol01
  have hreciprocal01 :
      ‖mixedForwardDifference first second 0 1 reciprocal
          (frequency + coordinateStep first)‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    rw [← hp10]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_one_le
      hlower hbound first second (point 1 0) hcontrol10
  have hreciprocal11 :
      ‖mixedForwardDifference first second 1 1 reciprocal frequency‖ ≤
        hodgeReciprocalMixedOneOneEnvelope lower bound :=
    norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound first second haxes frequency hstencil
  let a := mixedForwardDifference first second 1 1 numerator frequency *
    reciprocal (frequency + coordinateStep second + coordinateStep first)
  let b := mixedForwardDifference first second 0 1 numerator frequency *
    mixedForwardDifference first second 1 0 reciprocal
      (frequency + coordinateStep second)
  let c := mixedForwardDifference first second 1 0 numerator frequency *
    mixedForwardDifference first second 0 1 reciprocal
      (frequency + coordinateStep first)
  let d := numerator frequency *
    mixedForwardDifference first second 1 1 reciprocal frequency
  have ha : ‖a‖ ≤ 2 * hodgeReciprocalValueEnvelope lower := by
    dsimp [a]
    rw [norm_mul]
    exact mul_le_mul hnumerator11 hreciprocal00 (norm_nonneg _) (by positivity)
  have hb : ‖b‖ ≤
      (2 * bound + 1) * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [b]
    rw [norm_mul]
    exact mul_le_mul hnumerator01 hreciprocal10 (norm_nonneg _) (by positivity)
  have hc : ‖c‖ ≤
      (2 * bound + 1) * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [c]
    rw [norm_mul]
    exact mul_le_mul hnumerator10 hreciprocal01 (norm_nonneg _) (by positivity)
  have hd : ‖d‖ ≤
      3 * bound ^ 2 * hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [d]
    rw [norm_mul]
    exact mul_le_mul hnumerator00 hreciprocal11 (norm_nonneg _) (by positivity)
  rw [hentry, mixedForwardDifference_one_one_mul_eq]
  change ‖a + b + c + d‖ ≤ _
  rw [show a + b + c + d = a + (b + (c + d)) by ring]
  have hnorm : ‖a + (b + (c + d))‖ ≤
      ‖a‖ + (‖b‖ + (‖c‖ + ‖d‖)) := by
    simpa using norm_add_nine_le a b c d 0 0 0 0 0
  refine hnorm.trans ?_
  dsimp [hodgeJacobianEntryMixedOneOneEnvelope]
  have hmass := add_le_add ha (add_le_add hb (add_le_add hc hd))
  nlinarith

/-- Distinct-axis first/second variation of one genuine Hodge entry. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 1 2) :
    ‖mixedForwardDifference first second 1 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryMixedOneTwoEnvelope lower bound := by
  let numerator := fun current ↦ hodgeJacobianRatioNumerator current
    component coordinate input
  let reciprocal := hodgeReciprocal
  let point := twoAxisStencilPoint first second frequency
  have hentry :
      (fun current ↦ hodgeJacobianMultiplierEntry current component coordinate input) =
        fun current ↦ numerator current * reciprocal current := by
    funext current
    rw [hodgeJacobianMultiplierEntry_eq_ratio]
    simp [numerator, reciprocal, hodgeReciprocal,
      hodgeJacobianRatioNumerator, hodgeCrossBasisFactor, div_eq_mul_inv]
  have hp01 : point 0 1 = frequency + coordinateStep second := by
    simp [point, twoAxisStencilPoint]
  have hp02 : point 0 2 =
      frequency + coordinateStep second + coordinateStep second := by
    funext other
    simp [point, twoAxisStencilPoint]
    ring
  have hp10 : point 1 0 = frequency + coordinateStep first := by
    simp [point, twoAxisStencilPoint]
  have hp11 : point 1 1 =
      frequency + coordinateStep second + coordinateStep first := by
    unfold point twoAxisStencilPoint
    abel
  have hcontrol01 :
      TwoAxisStencilControlled lower bound first second (point 0 1) 1 1 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol02 :
      TwoAxisStencilControlled lower bound first second (point 0 2) 1 0 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol10 :
      TwoAxisStencilControlled lower bound first second (point 1 0) 0 2 :=
    hstencil.rebase (by omega) (by omega)
  have hcontrol11 :
      TwoAxisStencilControlled lower bound first second (point 1 1) 0 1 :=
    hstencil.rebase (by omega) (by omega)
  have hcoordinates : ∀ other : Fin 3, ‖(frequency other : ℂ)‖ ≤ bound := by
    simpa [twoAxisStencilPoint] using
      (hstencil 0 (by omega) 0 (by omega)).2
  have hnumerator12 :
      mixedForwardDifference first second 1 2 numerator frequency = 0 :=
    hodgeJacobianRatioNumerator_mixedForwardDifference_one_two_eq_zero
      first second frequency component coordinate input
  have hnumerator11 :
      ‖mixedForwardDifference first second 1 1 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_one_le_two
      first second frequency component coordinate input
  have hnumerator10 :
      ‖mixedForwardDifference first second 1 0 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_one_zero_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator02 :
      ‖mixedForwardDifference first second 0 2 numerator frequency‖ ≤ 2 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_two_le_two
      first second frequency component coordinate input
  have hnumerator01 :
      ‖mixedForwardDifference first second 0 1 numerator frequency‖ ≤
        2 * bound + 1 :=
    norm_hodgeJacobianRatioNumerator_mixedForwardDifference_zero_one_le
      hbound first second frequency hcoordinates component coordinate input
  have hnumerator00 : ‖numerator frequency‖ ≤ 3 * bound ^ 2 :=
    (norm_hodgeJacobianRatioNumerator_le_frequencySquared
      frequency component coordinate input).trans
        (frequencySquared_le_three_mul_sq hbound frequency hcoordinates)
  have hreciprocal01 :
      ‖mixedForwardDifference first second 0 1 reciprocal
          (frequency + coordinateStep second + coordinateStep first)‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    rw [← hp11]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_one_le
      hlower hbound first second (point 1 1) hcontrol11
  have hreciprocal02 :
      ‖mixedForwardDifference first second 0 2 reciprocal
          (frequency + coordinateStep first)‖ ≤
        hodgeReciprocalSecondEnvelope lower bound := by
    rw [← hp10]
    exact norm_hodgeReciprocal_mixedForwardDifference_zero_two_le
      hlower hbound first second (point 1 0) hcontrol10
  have hreciprocal10 :
      ‖mixedForwardDifference first second 1 0 reciprocal
          (frequency + coordinateStep second + coordinateStep second)‖ ≤
        hodgeReciprocalFirstEnvelope lower bound := by
    rw [← hp02]
    exact norm_hodgeReciprocal_mixedForwardDifference_one_zero_le
      hlower hbound first second (point 0 2) hcontrol02
  have hreciprocal11 :
      ‖mixedForwardDifference first second 1 1 reciprocal
          (frequency + coordinateStep second)‖ ≤
        hodgeReciprocalMixedOneOneEnvelope lower bound := by
    rw [← hp01]
    exact norm_hodgeReciprocal_mixedForwardDifference_one_one_le_of_controlled
      hlower hbound first second haxes (point 0 1) hcontrol01
  have hreciprocal12 :
      ‖mixedForwardDifference first second 1 2 reciprocal frequency‖ ≤
        hodgeReciprocalMixedOneTwoEnvelope lower bound :=
    norm_hodgeReciprocal_mixedForwardDifference_one_two_le_of_controlled
      hlower hbound first second haxes frequency hstencil
  let a := mixedForwardDifference first second 1 2 numerator frequency *
    reciprocal (frequency + coordinateStep second + coordinateStep second +
      coordinateStep first)
  let b := 2 * mixedForwardDifference first second 1 1 numerator frequency *
    mixedForwardDifference first second 0 1 reciprocal
      (frequency + coordinateStep second + coordinateStep first)
  let c := mixedForwardDifference first second 1 0 numerator frequency *
    mixedForwardDifference first second 0 2 reciprocal
      (frequency + coordinateStep first)
  let d := mixedForwardDifference first second 0 2 numerator frequency *
    mixedForwardDifference first second 1 0 reciprocal
      (frequency + coordinateStep second + coordinateStep second)
  let e := 2 * mixedForwardDifference first second 0 1 numerator frequency *
    mixedForwardDifference first second 1 1 reciprocal
      (frequency + coordinateStep second)
  let f := numerator frequency *
    mixedForwardDifference first second 1 2 reciprocal frequency
  have ha : ‖a‖ ≤ 0 := by simp [a, hnumerator12]
  have hb : ‖b‖ ≤ 4 * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [b]
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hproduct := mul_le_mul hnumerator11 hreciprocal01
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2)
    nlinarith [norm_nonneg
      (mixedForwardDifference first second 1 1 numerator frequency),
      norm_nonneg (mixedForwardDifference first second 0 1 reciprocal
        (frequency + coordinateStep second + coordinateStep first))]
  have hc : ‖c‖ ≤
      (2 * bound + 1) * hodgeReciprocalSecondEnvelope lower bound := by
    dsimp [c]
    rw [norm_mul]
    exact mul_le_mul hnumerator10 hreciprocal02 (norm_nonneg _) (by positivity)
  have hd : ‖d‖ ≤ 2 * hodgeReciprocalFirstEnvelope lower bound := by
    dsimp [d]
    rw [norm_mul]
    exact mul_le_mul hnumerator02 hreciprocal10 (norm_nonneg _) (by positivity)
  have he : ‖e‖ ≤
      2 * (2 * bound + 1) *
        hodgeReciprocalMixedOneOneEnvelope lower bound := by
    dsimp [e]
    rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have hproduct := mul_le_mul hnumerator01 hreciprocal11
      (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * bound + 1)
    nlinarith [norm_nonneg
      (mixedForwardDifference first second 0 1 numerator frequency),
      norm_nonneg (mixedForwardDifference first second 1 1 reciprocal
        (frequency + coordinateStep second))]
  have hf : ‖f‖ ≤
      3 * bound ^ 2 * hodgeReciprocalMixedOneTwoEnvelope lower bound := by
    dsimp [f]
    rw [norm_mul]
    exact mul_le_mul hnumerator00 hreciprocal12 (norm_nonneg _) (by positivity)
  rw [hentry, mixedForwardDifference_one_two_mul_eq]
  change ‖a + b + c + d + e + f‖ ≤ _
  rw [show a + b + c + d + e + f =
      a + (b + (c + (d + (e + f)))) by ring]
  have hnorm : ‖a + (b + (c + (d + (e + f))))‖ ≤
      ‖a‖ + (‖b‖ + (‖c‖ + (‖d‖ + (‖e‖ + ‖f‖)))) := by
    simpa using norm_add_nine_le a b c d e f 0 0 0
  refine hnorm.trans ?_
  dsimp [hodgeJacobianEntryMixedOneTwoEnvelope]
  have hmass := add_le_add ha
    (add_le_add hb (add_le_add hc (add_le_add hd (add_le_add he hf))))
  nlinarith

/-- Transposed first variation in the second displayed direction. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 0 1) :
    ‖mixedForwardDifference first second 0 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryFirstEnvelope lower bound := by
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_zero_le
    hlower hbound second first frequency component coordinate input hstencil.transpose
  unfold mixedForwardDifference at hraw ⊢
  simpa only [Function.iterate_zero_apply, Function.iterate_one] using hraw

/-- Transposed same-axis curvature in the second displayed direction. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_two_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 0 2) :
    ‖mixedForwardDifference first second 0 2
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntrySecondEnvelope lower bound := by
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
    hlower hbound second first frequency component coordinate input hstencil.transpose
  unfold mixedForwardDifference at hraw ⊢
  simpa only [Function.iterate_zero_apply] using hraw

/-- Transposed second/first variation; the two coordinate translations commute exactly. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_one_le
    {lower bound : ℝ} (hlower : 0 < lower) (hbound : 0 ≤ bound)
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) (component coordinate input : Fin 3)
    (hstencil : TwoAxisStencilControlled lower bound first second frequency 2 1) :
    ‖mixedForwardDifference first second 2 1
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤
      hodgeJacobianEntryMixedOneTwoEnvelope lower bound := by
  let entry := fun current ↦ hodgeJacobianMultiplierEntry current
    component coordinate input
  have hraw := norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le
    hlower hbound second first haxes.symm frequency component coordinate input
      hstencil.transpose
  have hcomm := congrFun
    (fwdDiff_iter_two_comm (coordinateStep second) (coordinateStep first) entry)
      frequency
  unfold mixedForwardDifference at hraw ⊢
  simp only [Function.iterate_one]
  rw [← hcomm]
  exact hraw

/-- Zero-order Hodge entry mass is globally bounded, including the totalized zero mode. -/
theorem norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_zero_zero_le_one
    (first second : Fin 3) (frequency : SpatialFrequency)
    (component coordinate input : Fin 3) :
    ‖mixedForwardDifference first second 0 0
      (fun current ↦ hodgeJacobianMultiplierEntry current
        component coordinate input) frequency‖ ≤ 1 := by
  simpa [mixedForwardDifference] using
    norm_hodgeJacobianMultiplierEntry_le_one frequency component coordinate input

section Audit

#print axioms mixedForwardDifference_one_two_mul_eq
#print axioms norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_two_zero_le
#print axioms norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_one_le
#print axioms norm_hodgeJacobianMultiplierEntry_mixedForwardDifference_one_two_le

end Audit

end Soma.Holonics.Millennium.NavierStokesAnnularHodgeLowerMixedVariation
