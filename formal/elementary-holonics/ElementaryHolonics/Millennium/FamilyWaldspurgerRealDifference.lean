import ElementaryHolonics.Millennium.FamilyThetaWaldspurgerBridge

/-!
# The Waldspurger--Tunnell seam as one exact real dimensionless difference

The existing family development isolates a complex-valued defect.  At the central point that
complex chart contains no additional degree of freedom: the theta integral, archimedean factor,
real period, and squared ternary coefficient are real.  This file removes the redundant imaginary
coordinate and returns the exact dimensionless comparison

`2 * centralValue / realPeriod - branchCount²`.

We prove that the continued central value is the complex cast of its real theta/archimedean
coordinate, that the new real difference is unchanged by reversing the count orientation, and that
its zero fibre is exactly the existing Waldspurger--Tunnell zero fibre.  Hence its vanishing closes
the already established BSD rank clause on every prime `p ≡ 3 (mod 8)`.

The correspondence asserting that this real difference vanishes is still `[open]`; this file does
not assume or prove it.  All chart removal and equivalences below are
`[proved-derived; formal-checked]`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyWaldspurgerRealDifference

open Complex MeasureTheory Set
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.FamilyCentralRatio
open Soma.Holonics.Millennium.FamilyThetaFE
open Soma.Holonics.Millennium.FamilyWaldspurgerGate

/-- [definition] The real coordinate underlying the stored complex archimedean factor. -/
def realArchimedeanFactor (p : ℕ) : ℝ :=
  Real.sqrt (32 * p ^ 2) / (2 * Real.pi)

theorem realArchimedeanFactor_pos {p : ℕ} (hp : 0 < p) :
    0 < realArchimedeanFactor p := by
  unfold realArchimedeanFactor
  positivity

theorem realArchimedeanFactor_cast (p : ℕ) :
    ((realArchimedeanFactor p : ℝ) : ℂ) = centralArchimedeanFactor p := by
  simp [realArchimedeanFactor, centralArchimedeanFactor]

/-- [definition] The actual real central-value coordinate returned by the theta integral after
division by its nonzero archimedean chart factor. -/
def realCentralValueCoordinate (p : ℕ) [Fact p.Prime] : ℝ :=
  (∫ t in Ioi (0 : ℝ), thetaP p t) / realArchimedeanFactor p

/-- [proved-derived; formal-checked] The continued central value has no hidden imaginary face: it
is exactly the cast of the real theta/archimedean coordinate. -/
theorem witnessCentralValue_eq_realCentralValueCoordinate
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1 =
      ((realCentralValueCoordinate p : ℝ) : ℂ) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hfactor : realArchimedeanFactor p ≠ 0 :=
    (realArchimedeanFactor_pos hp).ne'
  have hnormalization :=
    theWitnessCentralValueHasExactThetaNormalization p hp2
  rw [← realArchimedeanFactor_cast] at hnormalization
  rw [show ((realCentralValueCoordinate p : ℝ) : ℂ) =
      (((∫ t in Ioi (0 : ℝ), thetaP p t) : ℝ) : ℂ) /
        ((realArchimedeanFactor p : ℝ) : ℂ) by
      simp [realCentralValueCoordinate]]
  rw [eq_div_iff]
  · simpa [mul_comm] using hnormalization
  · exact_mod_cast hfactor

theorem witnessCentralValue_im_eq_zero
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1).im = 0 := by
  rw [witnessCentralValue_eq_realCentralValueCoordinate p hp2]
  simp

/-- [definition] The central ratio difference before deleting its redundant complex chart. -/
def complexCentralRatioDifference (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : ℂ :=
  (2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1 /
      ((realPeriod p : ℝ) : ℂ) -
    (((canonicalBranchCount p) ^ 2 : ℤ) : ℂ)

/-- [definition] The exact real, dimensionless Waldspurger--Tunnell difference. -/
def realCentralRatioDifference (p : ℕ) [Fact p.Prime] : ℝ :=
  2 * realCentralValueCoordinate p / realPeriod p -
    (canonicalBranchCount p : ℝ) ^ 2

/-- [proved-derived; formal-checked] The complex defect coordinate is exactly the cast of the real
difference; its imaginary coordinate was pure chart redundancy. -/
theorem realCentralRatioDifference_cast (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) :
    ((realCentralRatioDifference p : ℝ) : ℂ) = complexCentralRatioDifference p hp2 := by
  unfold realCentralRatioDifference complexCentralRatioDifference
  rw [witnessCentralValue_eq_realCentralValueCoordinate p hp2]
  push_cast
  ring

/-- [definition] The same real comparison with an arbitrary oriented count. -/
def realCentralRatioDifferenceForCount
    (p : ℕ) [Fact p.Prime] (count : ℤ) : ℝ :=
  2 * realCentralValueCoordinate p / realPeriod p - (count : ℝ) ^ 2

/-- [proved-derived; formal-checked] Reversing the lattice orientation changes the count but not
the comparison. -/
theorem realCentralRatioDifferenceForCount_neg
    (p : ℕ) [Fact p.Prime] (count : ℤ) :
    realCentralRatioDifferenceForCount p (-count) =
      realCentralRatioDifferenceForCount p count := by
  unfold realCentralRatioDifferenceForCount
  push_cast
  ring

theorem realCentralRatioDifference_eq_forCanonicalCount
    (p : ℕ) [Fact p.Prime] :
    realCentralRatioDifference p =
      realCentralRatioDifferenceForCount p (canonicalBranchCount p) :=
  rfl

/-- [proved-derived; formal-checked] The zero fibre of the dimensionless complex difference is
exactly the normalized central-ratio identity. -/
theorem complexCentralRatioDifference_eq_zero_iff
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : 0 < p) :
    complexCentralRatioDifference p hp2 = 0 ↔
      (2 : ℂ) * (FamilyWitness.theWitnessAtEveryOddPrime p hp2).L 1 =
        (((canonicalBranchCount p) ^ 2 : ℤ) : ℂ) *
          ((realPeriod p : ℝ) : ℂ) := by
  have hperiod : ((realPeriod p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast FamilyPeriod.theRealPeriodIsNotNull hp
  unfold complexCentralRatioDifference
  rw [sub_eq_zero, div_eq_iff hperiod]

/-- [proved-derived; formal-checked] The new real null fibre and the existing
Waldspurger--Tunnell null fibre are the same receiver occurrence. -/
theorem realCentralRatioDifference_eq_zero_iff_waldspurgerTunnellDefect_eq_zero
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3) :
    realCentralRatioDifference p = 0 ↔ waldspurgerTunnellDefect p = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp2 : p ≠ 2 := by omega
  rw [← Complex.ofReal_eq_zero]
  rw [realCentralRatioDifference_cast p hp2]
  rw [complexCentralRatioDifference_eq_zero_iff hp2 hp]
  exact centralRatio_iff_waldspurgerTunnellDefect_eq_zero hp8

/-- [proved-derived; formal-checked] Vanishing of the exact real difference closes the BSD rank
clause on the complete positive-root-number prime branch. -/
theorem rankClause_of_realCentralRatioDifference_eq_zero
    {p : ℕ} [Fact p.Prime] (hp8 : p % 8 = 3)
    (hzero : realCentralRatioDifference p = 0) :
    TheRankClause p (FamilyWitness.theWitnessAtEveryOddPrime p (by omega)) :=
  rankClause_of_waldspurgerTunnellDefect_eq_zero hp8
    ((realCentralRatioDifference_eq_zero_iff_waldspurgerTunnellDefect_eq_zero hp8).mp hzero)

section Audit

#print axioms witnessCentralValue_eq_realCentralValueCoordinate
#print axioms witnessCentralValue_im_eq_zero
#print axioms realCentralRatioDifference_cast
#print axioms realCentralRatioDifferenceForCount_neg
#print axioms complexCentralRatioDifference_eq_zero_iff
#print axioms realCentralRatioDifference_eq_zero_iff_waldspurgerTunnellDefect_eq_zero
#print axioms rankClause_of_realCentralRatioDifference_eq_zero

end Audit

end Soma.Holonics.Millennium.FamilyWaldspurgerRealDifference
