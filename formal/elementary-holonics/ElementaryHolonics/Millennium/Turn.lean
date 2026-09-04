import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.BigOperators

/-!
# The turn — what the exponential deletes, and what each chart can still store

The exponential carries the additive chart to the multiplicative one.  It is not injective, and
the complex kernel is a lattice of whole turns.  Over the real chart this file proves only
injectivity and the positive image; any quotient/cokernel interpretation is left unformalized.

That is the whole content of "a sign is what remains of a phase after the winding is deleted",
and this file discharges it.

The second half is the pair of branch maps that read a nested radical of two as a binary
expansion of an angle.  Both are half-angle laws; the sign selects orientation.

Every `theorem` here is discharged.
-/

namespace Soma.Holonics.Millennium.Turn

open Real Complex
open scoped BigOperators

/-! ## 1. The complex chart stores the deleted turn in its kernel -/

/-- **The whole turn generates what the exponential deletes.**

*Aside: `ker(exp : ℂ → ℂˣ) = 2πiℤ`.* -/
theorem theWholeTurnIsWhatTheExponentialDeletes (x : ℂ) :
    Complex.exp x = 1 ↔ ∃ n : ℤ, x = n * (2 * Real.pi * Complex.I) :=
  Complex.exp_eq_one_iff

/-- **A whole turn changes nothing multiplicatively.**  The additive chart moves; the
multiplicative chart does not see it. -/
theorem theWholeTurnIsInvisibleToTheMultiplicativeChart (x : ℂ) :
    Complex.exp (x + 2 * Real.pi * Complex.I) = Complex.exp x := by
  rw [Complex.exp_add]
  simp [Complex.exp_two_pi_mul_I]

/-- **The half turn is the sign.**  This is the substitution `-1 = e^{iπ}` as a theorem, and it
is why an inversion in an exponent is a half turn rather than a separate species of quantity. -/
theorem theHalfTurnIsTheSign : Complex.exp (Real.pi * Complex.I) = -1 :=
  Complex.exp_pi_mul_I

/-! ## 2. The real chart is injective and has positive image -/

/-- **The real chart cannot store a turn: the real exponential deletes nothing.** -/
theorem theRealChartHasNoKernel : Function.Injective Real.exp :=
  Real.exp_injective

/-- **The real exponential has exactly the positive reals as its image.**

No quotient or cokernel is constructed by this theorem. -/
theorem theRealExponentialHasPositiveImage (x : ℝ) :
    (∃ u : ℝ, Real.exp u = x) ↔ 0 < x := by
  constructor
  · rintro ⟨u, rfl⟩
    exact Real.exp_pos u
  · intro h
    exact ⟨Real.log x, Real.exp_log h⟩

/-- Restated as a refusal: a negative real is never reached by the real exponential. -/
theorem theRealExponentialMissesNegativeInputs {x : ℝ} (hx : x < 0) :
    ¬ ∃ u : ℝ, Real.exp u = x := by
  rw [theRealExponentialHasPositiveImage]
  exact not_lt.mpr hx.le

/-! ## 3. Intrinsic turn calibration from a finite arc partition

The scalar normally written as `π` is not taken as the definition of an arbitrary turn.  A
finite family of addressed arc occurrences first returns its integrated length.  A positive
radial calibration then supplies the numerical half- and full-turn receivers.  Only a separate
Euclidean-circle witness identifies those receivers with `π` and `2π`.

This is deliberately the metric calibration layer, not yet a polygonal adjacency or solid-torus
cellulation.  In particular, the finite index records distinct arc occurrences but does not claim
that they have been ordered into a closed path.
-/

/-- Exact metric testimony attached to a finite population of arc occurrences. -/
structure ArcPartition (ι : Type*) [Fintype ι] where
  arcLength : ι → ℝ
  arcLength_nonneg : ∀ i, 0 ≤ arcLength i

namespace ArcPartition

/-- The integrated length is the exact finite sum of the addressed arc lengths. -/
def integratedLength {ι : Type*} [Fintype ι] (partition : ArcPartition ι) : ℝ :=
  ∑ i, partition.arcLength i

/-- A finite partition with nonnegative local lengths has nonnegative integrated length. -/
theorem integratedLength_nonneg {ι : Type*} [Fintype ι] (partition : ArcPartition ι) :
    0 ≤ partition.integratedLength :=
  Finset.sum_nonneg fun i _ => partition.arcLength_nonneg i

end ArcPartition

/-- A numerical turn receiver formed from an exact arc partition and a positive radial scale. -/
structure TurnCalibration (ι : Type*) [Fintype ι] where
  partition : ArcPartition ι
  radialScale : ℝ
  radialScale_pos : 0 < radialScale

namespace TurnCalibration

/-- The circumference receiver retains the integrated arc population rather than postulating
`2πr`. -/
def circumference {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) : ℝ :=
  calibration.partition.integratedLength

/-- The half-turn receiver `C/(2r)`. -/
noncomputable def halfTurn {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) : ℝ :=
  calibration.circumference / (2 * calibration.radialScale)

/-- The full-turn receiver `C/r`. -/
noncomputable def fullTurn {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) : ℝ :=
  calibration.circumference / calibration.radialScale

/-- The full-turn receiver is exactly twice the half-turn receiver. -/
theorem fullTurn_eq_two_mul_halfTurn {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) :
    calibration.fullTurn = 2 * calibration.halfTurn := by
  rw [fullTurn, halfTurn]
  field_simp [ne_of_gt calibration.radialScale_pos]

/-- The additional constitutive witness that the integrated arcs calibrate one Euclidean circle.
It is a property of the carrier, not a definition of every finite loop. -/
def IsEuclideanCircle {ι : Type*} [Fintype ι] (calibration : TurnCalibration ι) : Prop :=
  calibration.circumference = 2 * Real.pi * calibration.radialScale

/-- A Euclidean-circle witness decodes the intrinsic half-turn receiver to `π`. -/
theorem halfTurn_eq_pi_of_isEuclideanCircle {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (hcircle : calibration.IsEuclideanCircle) :
    calibration.halfTurn = Real.pi := by
  rw [halfTurn, hcircle]
  field_simp [ne_of_gt calibration.radialScale_pos]

/-- A Euclidean-circle witness decodes the intrinsic full-turn receiver to `2π`. -/
theorem fullTurn_eq_two_pi_of_isEuclideanCircle {ι : Type*} [Fintype ι]
    (calibration : TurnCalibration ι) (hcircle : calibration.IsEuclideanCircle) :
    calibration.fullTurn = 2 * Real.pi := by
  rw [calibration.fullTurn_eq_two_mul_halfTurn,
    calibration.halfTurn_eq_pi_of_isEuclideanCircle hcircle]

end TurnCalibration

/-- Four unit arc occurrences at unit radial scale.  This is an exact finite calibration fixture;
it makes no circularity claim. -/
def fourUnitArcCalibration : TurnCalibration (Fin 4) where
  partition := {
    arcLength := fun _ => 1
    arcLength_nonneg := by simp
  }
  radialScale := 1
  radialScale_pos := by norm_num

/-- The fixture's integrated circumference is exactly four. -/
@[simp] theorem fourUnitArcCalibration_circumference :
    fourUnitArcCalibration.circumference = 4 := by
  simp [fourUnitArcCalibration, TurnCalibration.circumference,
    ArcPartition.integratedLength]

/-- The fixture's intrinsic half-turn receiver is exactly two. -/
@[simp] theorem fourUnitArcCalibration_halfTurn :
    fourUnitArcCalibration.halfTurn = 2 := by
  rw [TurnCalibration.halfTurn, fourUnitArcCalibration_circumference]
  norm_num [fourUnitArcCalibration]

/-- A finite arc partition and radial scale do not by themselves force `C/(2r) = π`. -/
theorem finiteArcCalibrationDoesNotForcePi :
    fourUnitArcCalibration.halfTurn ≠ Real.pi := by
  rw [fourUnitArcCalibration_halfTurn]
  nlinarith [Real.pi_gt_three]

/-- Consequently the finite calibration fixture cannot carry a Euclidean-circle witness. -/
theorem fourUnitArcCalibration_isNotEuclideanCircle :
    ¬ fourUnitArcCalibration.IsEuclideanCircle := by
  intro hcircle
  exact finiteArcCalibrationDoesNotForcePi
    (fourUnitArcCalibration.halfTurn_eq_pi_of_isEuclideanCircle hcircle)

/-! ## 4. The two branch maps of a nested radical of two are the half-angle laws

Working in the coordinate `x = 2 cos θ`, the two nested-radical branches are contractions of
ratio one half on the turn.  The plus branch preserves orientation; the minus branch reverses
it.  A sign word is therefore a binary expansion of an angle, in the reflected code. -/

/-- **The plus branch halves the turn.**

`√(2 + 2 cos θ) = 2 cos(θ/2)`, so in the coordinate `x = 2 cos θ` the map `x ↦ √(2 + x)` is
`θ ↦ θ/2`.

*Aside: this is the cosine half-angle law, and `x ↦ x² − 2` is its inverse — the second
Chebyshev polynomial in the `2 cos` normalization, which the integer form calls Dickson.* -/
theorem thePlusBranchHalvesTheTurn {θ : ℝ} (hl : -Real.pi ≤ θ) (hr : θ ≤ Real.pi) :
    Real.sqrt (2 + 2 * Real.cos θ) = 2 * Real.cos (θ / 2) := by
  rw [Real.cos_half hl hr]
  rw [show (2 : ℝ) + 2 * Real.cos θ = 4 * ((1 + Real.cos θ) / 2) by ring]
  rw [Real.sqrt_mul (by norm_num)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The minus branch halves the turn and reflects it.**

`√(2 − 2 cos θ) = 2 sin(θ/2)`, and `sin(θ/2) = cos((π − θ)/2)`, so in the same coordinate the
map `x ↦ √(2 − x)` is `θ ↦ (π − θ)/2` — a half-turn contraction that reverses orientation. -/
theorem theMinusBranchHalvesTheTurnAndReflectsIt {θ : ℝ} (hl : 0 ≤ θ) (hr : θ ≤ 2 * Real.pi) :
    Real.sqrt (2 - 2 * Real.cos θ) = 2 * Real.sin (θ / 2) := by
  rw [Real.sin_half_eq_sqrt hl hr]
  rw [show (2 : ℝ) - 2 * Real.cos θ = 4 * ((1 - Real.cos θ) / 2) by ring]
  rw [Real.sqrt_mul (by norm_num)]
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- **The minus branch is the plus branch at the reflected angle.**  The two branches differ by
the involution `θ ↦ π − θ`, which is the orientation reversal. -/
theorem theMinusBranchIsThePlusBranchReflected (θ : ℝ) :
    Real.sin (θ / 2) = Real.cos ((Real.pi - θ) / 2) := by
  rw [show (Real.pi - θ) / 2 = Real.pi / 2 - θ / 2 by ring, Real.cos_pi_div_two_sub]

/-! ## 5. The first value the crystallographic filter refuses

The rational values of `2 cos` at a rational turn form a five-element table.  The first turn
outside it that a periodic sign word reaches is the fifth, and its value is the golden ratio. -/

/-- **The golden ratio is twice the cosine of a fifth of a half-turn.**

*Aside: `2 cos(π/5) = φ`.  This is the value a period-two sign word reaches, and five is the
first order that is finite and not crystallographic — the first refusal of the rational table.* -/
theorem theGoldenRatioIsTwiceACosineOfTheFifthTurn :
    2 * Real.cos (Real.pi / 5) = (1 + Real.sqrt 5) / 2 := by
  rw [Real.cos_pi_div_five]; ring

/-- **That value satisfies the period-two fixed-point equation.**

`x² = x + 1` is exactly the relation the alternating sign word forces: with `y = √(2 − x)` and
`x = √(2 + y)` one gets `x − y = 1`, hence `x² − x − 1 = 0`. -/
theorem theFifthTurnValueSolvesThePeriodTwoRelation :
    (2 * Real.cos (Real.pi / 5)) ^ 2 = 2 * Real.cos (Real.pi / 5) + 1 := by
  rw [theGoldenRatioIsTwiceACosineOfTheFifthTurn]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [h5]

/-- **And the reciprocal turn is the other root.**  `2 cos(2π/5) = 1/φ`, the second value the
period-two word reaches, differing from the first by exactly one. -/
theorem theDoubledFifthTurnIsTheOtherRoot :
    2 * Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 2 := by
  have h : (2 : ℝ) * Real.pi / 5 = 2 * (Real.pi / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

/-- **The two period-two values differ by exactly one.**  That difference is the fixed-point
relation the alternating word forces, and it is why the golden ratio and its reciprocal appear
together rather than separately. -/
theorem thePeriodTwoValuesDifferByOne :
    2 * Real.cos (Real.pi / 5) - 2 * Real.cos (2 * Real.pi / 5) = 1 := by
  rw [theGoldenRatioIsTwiceACosineOfTheFifthTurn, theDoubledFifthTurnIsTheOtherRoot]
  ring

/-! ## Audit -/

#print axioms ArcPartition.integratedLength_nonneg
#print axioms TurnCalibration.fullTurn_eq_two_mul_halfTurn
#print axioms TurnCalibration.halfTurn_eq_pi_of_isEuclideanCircle
#print axioms TurnCalibration.fullTurn_eq_two_pi_of_isEuclideanCircle
#print axioms finiteArcCalibrationDoesNotForcePi
#print axioms fourUnitArcCalibration_isNotEuclideanCircle

end Soma.Holonics.Millennium.Turn
