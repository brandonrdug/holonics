import ElementaryHolonics.Millennium.FamilyTunnellBrandtTestVector

/-!
# The exact two-class interchange law

The Brandt receiver has two retained classes.  This file isolates the finite
algebra needed by the next source-specific passage: a two-by-two integer
neighbor action has one common row aperture, its two off-diagonal transports
interchange exactly, and its diagonal transports are then forced to agree.
The signed class difference is consequently an eigen-current with eigenvalue
the diagonal-minus-off-diagonal calibration.

No Brandt matrix or Hecke eigenlaw is asserted here.  The structure below is a
typed interface for the missing source correspondence; its entries remain
explicit integer returns and the source-specific theorem is a hypothesis of a
conditional composition theorem, never an axiom hidden in a definition.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtTwoClassInterchange

open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellThetaCarrier
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellOddHeckeDoubleCount

/-! ## The finite two-class action -/

/-- An exact two-class neighbor action.  `aperture` is the common returned row
count; the four entries retain the two source and two target classes. -/
structure TwoClassNeighborAction (lambda : ℤ) where
  diagonalFirst : ℤ
  offDiagonalFirst : ℤ
  offDiagonalSecond : ℤ
  diagonalSecond : ℤ
  aperture : ℤ
  firstRow : diagonalFirst + offDiagonalFirst = aperture
  secondRow : offDiagonalSecond + diagonalSecond = aperture
  offDiagonalInterchange : offDiagonalFirst = offDiagonalSecond
  normOneSignedCalibration : diagonalFirst - offDiagonalFirst = lambda

/-- The two-class action as a retained integer matrix, with rows indexed by
source class and columns by returned class. -/
def TwoClassNeighborAction.matrix {lambda : ℤ}
    (A : TwoClassNeighborAction lambda) : Fin 2 → Fin 2 → ℤ
  | 0, 0 => A.diagonalFirst
  | 0, 1 => A.offDiagonalFirst
  | 1, 0 => A.offDiagonalSecond
  | 1, 1 => A.diagonalSecond
  | _, _ => 0

/-- Exact off-diagonal interchange is the matrix symmetry across the class
diagonal. -/
theorem TwoClassNeighborAction.matrix_offDiagonal_interchange
    {lambda : ℤ} (A : TwoClassNeighborAction lambda) :
    A.matrix 0 1 = A.matrix 1 0 := by
  simpa [TwoClassNeighborAction.matrix] using A.offDiagonalInterchange

/-- Common row aperture plus off-diagonal interchange forces equality of the
two diagonal returns. -/
theorem TwoClassNeighborAction.diagonal_interchange
    {lambda : ℤ} (A : TwoClassNeighborAction lambda) :
    A.diagonalFirst = A.diagonalSecond := by
  linarith [A.firstRow, A.secondRow, A.offDiagonalInterchange]

/-- The same forced equality in matrix coordinates. -/
theorem TwoClassNeighborAction.matrix_diagonal_interchange
    {lambda : ℤ} (A : TwoClassNeighborAction lambda) :
    A.matrix 0 0 = A.matrix 1 1 := by
  simpa [TwoClassNeighborAction.matrix] using A.diagonal_interchange

/-- The signed two-class difference returned by the action on a coefficient
pair `(r₁,r₂)`. -/
def TwoClassNeighborAction.differenceReturn {lambda : ℤ}
    (A : TwoClassNeighborAction lambda) (r₁ r₂ : ℤ) : ℤ :=
  (A.diagonalFirst * r₁ + A.offDiagonalFirst * r₂) -
    (A.offDiagonalSecond * r₁ + A.diagonalSecond * r₂)

/-- The exact cancellation/interchange identity for the returned difference. -/
theorem TwoClassNeighborAction.differenceReturn_eq_calibration_mul
    {lambda : ℤ} (A : TwoClassNeighborAction lambda) (r₁ r₂ : ℤ) :
    A.differenceReturn r₁ r₂ = lambda * (r₁ - r₂) := by
  unfold TwoClassNeighborAction.differenceReturn
  calc
    (A.diagonalFirst * r₁ + A.offDiagonalFirst * r₂) -
        (A.offDiagonalSecond * r₁ + A.diagonalSecond * r₂) =
        (A.diagonalFirst - A.offDiagonalFirst) * (r₁ - r₂) := by
          rw [A.offDiagonalInterchange, ← A.diagonal_interchange]
          ring
    _ = lambda * (r₁ - r₂) := by rw [A.normOneSignedCalibration]

/-- The common row aperture is also the sum of the diagonal and
off-diagonal returns in either class. -/
theorem TwoClassNeighborAction.secondRow_rewritten
    {lambda : ℤ} (A : TwoClassNeighborAction lambda) :
    A.diagonalSecond + A.offDiagonalSecond = A.aperture := by
  linarith [A.secondRow]

/-- A source-specific action family carries the same signed calibration at all
coefficient indices.  This is the uniform-in-`n` interface required by a
local-to-global successor law. -/
structure UniformTwoClassNeighborAction (lambda : ℤ) where
  actionAt : ℕ → TwoClassNeighborAction lambda

/-! ## The weighted source law

Brandt self-adjointness is naturally weighted by stabilizer/unit indices.  The
unweighted interchange used above is therefore obtained only after the two
retained classes have been proved to carry the same nonzero unit weight.  This
section keeps that obligation visible instead of silently replacing weighted
self-adjointness by matrix symmetry. -/

/-- A two-class action before equal unit weights have been established. -/
structure WeightedTwoClassNeighborAction (lambda : ℤ) where
  diagonalFirst : ℤ
  offDiagonalFirst : ℤ
  offDiagonalSecond : ℤ
  diagonalSecond : ℤ
  aperture : ℤ
  unitWeightFirst : ℤ
  unitWeightSecond : ℤ
  unitWeightFirst_ne_zero : unitWeightFirst ≠ 0
  unitWeightSecond_ne_zero : unitWeightSecond ≠ 0
  firstRow : diagonalFirst + offDiagonalFirst = aperture
  secondRow : offDiagonalSecond + diagonalSecond = aperture
  weightedOffDiagonalInterchange :
    unitWeightFirst * offDiagonalFirst =
      unitWeightSecond * offDiagonalSecond
  normOneSignedCalibration : diagonalFirst - offDiagonalFirst = lambda

/-- Equal nonzero unit weights turn weighted Brandt self-adjointness into the
literal off-diagonal interchange needed by the signed class receiver. -/
theorem WeightedTwoClassNeighborAction.offDiagonalInterchange_of_equal_weight
    {lambda : ℤ} (A : WeightedTwoClassNeighborAction lambda)
    (hweight : A.unitWeightFirst = A.unitWeightSecond) :
    A.offDiagonalFirst = A.offDiagonalSecond := by
  apply mul_left_cancel₀ A.unitWeightFirst_ne_zero
  calc
    A.unitWeightFirst * A.offDiagonalFirst =
        A.unitWeightSecond * A.offDiagonalSecond :=
      A.weightedOffDiagonalInterchange
    _ = A.unitWeightFirst * A.offDiagonalSecond := by rw [hweight]

/-- The exact passage from the source-weighted Brandt action to the raw
two-class action.  The equal-weight proof is an explicit input. -/
def WeightedTwoClassNeighborAction.toTwoClassNeighborAction
    {lambda : ℤ} (A : WeightedTwoClassNeighborAction lambda)
    (hweight : A.unitWeightFirst = A.unitWeightSecond) :
    TwoClassNeighborAction lambda where
  diagonalFirst := A.diagonalFirst
  offDiagonalFirst := A.offDiagonalFirst
  offDiagonalSecond := A.offDiagonalSecond
  diagonalSecond := A.diagonalSecond
  aperture := A.aperture
  firstRow := A.firstRow
  secondRow := A.secondRow
  offDiagonalInterchange := A.offDiagonalInterchange_of_equal_weight hweight
  normOneSignedCalibration := A.normOneSignedCalibration

/-- Weighted self-adjointness, equal unit weights, and norm-one calibration
already imply the calibrated signed-difference law. -/
theorem WeightedTwoClassNeighborAction.differenceReturn_eq_calibration_mul
    {lambda : ℤ} (A : WeightedTwoClassNeighborAction lambda)
    (hweight : A.unitWeightFirst = A.unitWeightSecond) (r₁ r₂ : ℤ) :
    (A.toTwoClassNeighborAction hweight).differenceReturn r₁ r₂ =
      lambda * (r₁ - r₂) := by
  exact (A.toTwoClassNeighborAction hweight).differenceReturn_eq_calibration_mul r₁ r₂

/-! ## The Brandt difference receiver -/

/-- The two retained finite Brandt populations, read as integer class counts.
The casts are part of the receiver chart and are not discarded. -/
def brandtClassDifference (n : ℕ) : ℤ :=
  ((brandtFirstPopulation n).card : ℤ) -
    ((brandtSecondPopulation n).card : ℤ)

/-- The source-specific coefficient is exactly the returned Brandt class
difference. -/
theorem fullTunnellThetaCoefficient_eq_classDifference (n : ℕ) :
    fullTunnellThetaCoefficient n = brandtClassDifference n := by
  exact fullTunnellThetaCoefficient_eq_brandtDifference n

/-- Applying a uniform two-class action to the two Brandt class populations
returns the calibrated multiple of the complete Tunnell coefficient. -/
theorem uniformAction_differenceReturn_eq_lambda_mul_fullCoefficient
    {lambda : ℤ} (A : UniformTwoClassNeighborAction lambda) (n : ℕ) :
    (A.actionAt n).differenceReturn
        ((brandtFirstPopulation n).card : ℤ)
        ((brandtSecondPopulation n).card : ℤ) =
      lambda * fullTunnellThetaCoefficient n := by
  rw [(A.actionAt n).differenceReturn_eq_calibration_mul]
  rw [fullTunnellThetaCoefficient_eq_classDifference n]
  rfl

/-! ## Source-specific bridge to the odd-prime neighbor receiver -/

/-- Exact conditional composition with the already constructed odd-prime
neighbor return.  The remaining source-specific statement is exposed as the
single equality `hsource`; no open Brandt or Hecke law is named as proved. -/
theorem oddTunnellNeighborReturn_eq_lambda_mul_fullCoefficient_of_source
    {p : ℕ} [Fact p.Prime] {lambda : ℤ}
    (hp2 : p ≠ 2) (A : UniformTwoClassNeighborAction lambda) (n : ℕ)
    (hsource :
      oddTunnellNeighborReturn (p := p) hp2 n =
        (A.actionAt n).differenceReturn
          ((brandtFirstPopulation n).card : ℤ)
          ((brandtSecondPopulation n).card : ℤ)) :
    oddTunnellNeighborReturn (p := p) hp2 n =
      lambda * fullTunnellThetaCoefficient n := by
  rw [hsource]
  exact uniformAction_differenceReturn_eq_lambda_mul_fullCoefficient A n

/-- The source interface can equivalently be supplied directly as a complete
uniform family of returned differences.  This theorem is useful when the
neighbor construction has already fused its two class fibres. -/
theorem oddTunnellNeighborReturn_eq_lambda_mul_fullCoefficient_of_uniform_source
    {p : ℕ} [Fact p.Prime] {lambda : ℤ}
    (hp2 : p ≠ 2) (A : UniformTwoClassNeighborAction lambda)
    (hsource : ∀ n : ℕ,
      oddTunnellNeighborReturn (p := p) hp2 n =
        (A.actionAt n).differenceReturn
          ((brandtFirstPopulation n).card : ℤ)
          ((brandtSecondPopulation n).card : ℤ)) :
    ∀ n : ℕ,
      oddTunnellNeighborReturn (p := p) hp2 n =
        lambda * fullTunnellThetaCoefficient n := by
  intro n
  exact oddTunnellNeighborReturn_eq_lambda_mul_fullCoefficient_of_source
    hp2 A n (hsource n)

#print axioms TwoClassNeighborAction.diagonal_interchange
#print axioms TwoClassNeighborAction.differenceReturn_eq_calibration_mul
#print axioms WeightedTwoClassNeighborAction.offDiagonalInterchange_of_equal_weight
#print axioms WeightedTwoClassNeighborAction.differenceReturn_eq_calibration_mul
#print axioms fullTunnellThetaCoefficient_eq_classDifference
#print axioms uniformAction_differenceReturn_eq_lambda_mul_fullCoefficient
#print axioms oddTunnellNeighborReturn_eq_lambda_mul_fullCoefficient_of_source

end Soma.Holonics.Millennium.FamilyTunnellBrandtTwoClassInterchange
