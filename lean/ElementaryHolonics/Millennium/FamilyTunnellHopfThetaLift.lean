import ElementaryHolonics.Millennium.FamilyTunnellHopfThetaCensus
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The modulo-four Hopf census as an exact theta-current identity

The preceding finite residue theorem is not left at the 256-cell receiver.
This file evaluates it in the formal-power-series body carried by the three
addressed square streams modulo four.  No convergence, floating coordinate, or
modular-form classification enters: coefficients remain exact integers.

The opposite odd streams are identified by the explicit coordinate-negation
equivalence, retaining the witness which makes the fold lawful.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift

open Finset
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus

abbrev IntegerSeries := PowerSeries ℤ

/-! ## Receiver transport of the finite residue body -/

/-- Evaluation retains every folded exponent address while changing only the
coefficient body. -/
def residueEvaluate {R : Type*} [CommRing R] (a b c : R)
    (P : ResiduePolynomial) : R :=
  ∑ e : ResidueExponent,
    (P e : R) * a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val

def differenceExpandedPolynomial : ResiduePolynomial := fun e =>
  if e = ((3 : Fin 5), (1 : Fin 5), (0 : Fin 5)) then 8
  else if e = ((2 : Fin 5), (1 : Fin 5), (1 : Fin 5)) then -8
  else if e = ((1 : Fin 5), (1 : Fin 5), (2 : Fin 5)) then -8
  else if e = ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5)) then 8
  else 0

def differenceSupport : Finset ResidueExponent :=
  {((3 : Fin 5), (1 : Fin 5), (0 : Fin 5)),
    ((2 : Fin 5), (1 : Fin 5), (1 : Fin 5)),
    ((1 : Fin 5), (1 : Fin 5), (2 : Fin 5)),
    ((0 : Fin 5), (1 : Fin 5), (3 : Fin 5))}

private theorem differenceFactorizedPolynomial_eq_expanded :
    differenceFactorizedPolynomial = differenceExpandedPolynomial := by
  rfl

/-- The four surviving monomials return the literal factor
`8 B (A+C) (A-C)²` in every commutative receiver. -/
theorem residueEvaluate_differenceFactorized {R : Type*} [CommRing R]
    (a b c : R) :
    residueEvaluate a b c differenceFactorizedPolynomial =
      8 * b * (a + c) * (a - c) ^ 2 := by
  rw [differenceFactorizedPolynomial_eq_expanded]
  unfold residueEvaluate
  rw [← Finset.sum_subset (Finset.subset_univ differenceSupport)]
  · simp [differenceSupport, differenceExpandedPolynomial]
    ring
  · intro e heUniv heSupport
    simp [differenceSupport] at heSupport
    simp [differenceExpandedPolynomial, heSupport]

/-- The census equality commutes with every declared commutative receiver. -/
theorem residueEvaluate_hopfDifference {R : Type*} [CommRing R]
    (a b c : R) :
    2 * residueEvaluate a b c hopfSourceResiduePolynomial -
        residueEvaluate a b c oddFourSquareResiduePolynomial =
      8 * b * (a + c) * (a - c) ^ 2 := by
  have hEval := congrArg (residueEvaluate a b c) hopfResidueDifference_eq
  rw [residueEvaluate_differenceFactorized] at hEval
  unfold residueEvaluate at hEval ⊢
  simp only [residueSub, residueScale] at hEval
  calc
    2 * (∑ e : ResidueExponent,
          (hopfSourceResiduePolynomial e : R) * a ^ e.1.val *
            b ^ e.2.1.val * c ^ e.2.2.val) -
        ∑ e : ResidueExponent,
          (oddFourSquareResiduePolynomial e : R) * a ^ e.1.val *
            b ^ e.2.1.val * c ^ e.2.2.val =
      ∑ e : ResidueExponent,
        ((2 * hopfSourceResiduePolynomial e -
            oddFourSquareResiduePolynomial e : ℤ) : R) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro e he
            push_cast
            ring
    _ = 8 * b * (a + c) * (a - c) ^ 2 := hEval

/-- Complete bounded representatives of one square coefficient and one
modulo-four orientation. -/
def quarterSquarePopulation (r : QuarterResidue) (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun x =>
    x ^ 2 = (n : ℤ) ∧ (x : ZMod 4) = r.val

/-- The exact unary square stream of one modulo-four orientation. -/
def quarterSquareTheta (r : QuarterResidue) : IntegerSeries :=
  PowerSeries.mk fun n => ((quarterSquarePopulation r n).card : ℤ)

@[simp] theorem coeff_quarterSquareTheta (r : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n (quarterSquareTheta r) =
      ((quarterSquarePopulation r n).card : ℤ) := by
  simp [quarterSquareTheta]

/-- Negation transports the `1 mod 4` square occurrence population to the
`3 mod 4` population without changing its square address. -/
def oddQuarterNegationEquiv (n : ℕ) :
    {x // x ∈ quarterSquarePopulation 1 n} ≃
      {x // x ∈ quarterSquarePopulation 3 n} where
  toFun x := ⟨-x.1, by
    rcases Finset.mem_filter.mp x.2 with ⟨hxBox, hxSquare, hxResidue⟩
    simp only [quarterSquarePopulation, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hxBox ⊢
      constructor <;> linarith [hxBox.1, hxBox.2]
    · nlinarith
    · calc
        ((-x.1 : ℤ) : ZMod 4) = -(x.1 : ZMod 4) := by norm_num
        _ = -(1 : ZMod 4) := congrArg Neg.neg hxResidue
        _ = (3 : ZMod 4) := by decide⟩
  invFun x := ⟨-x.1, by
    rcases Finset.mem_filter.mp x.2 with ⟨hxBox, hxSquare, hxResidue⟩
    simp only [quarterSquarePopulation, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hxBox ⊢
      constructor <;> linarith [hxBox.1, hxBox.2]
    · nlinarith
    · calc
        ((-x.1 : ℤ) : ZMod 4) = -(x.1 : ZMod 4) := by norm_num
        _ = -(3 : ZMod 4) := congrArg Neg.neg hxResidue
        _ = (1 : ZMod 4) := by decide⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

theorem quarterSquarePopulation_one_card_eq_three (n : ℕ) :
    (quarterSquarePopulation 1 n).card =
      (quarterSquarePopulation 3 n).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr (oddQuarterNegationEquiv n)

/-- The two odd orientations have the same complete formal square stream. -/
theorem quarterSquareTheta_one_eq_three :
    quarterSquareTheta 1 = quarterSquareTheta 3 := by
  apply PowerSeries.ext
  intro n
  simp [quarterSquarePopulation_one_card_eq_three]

/-- Evaluation of the residue body at the three addressed square streams. -/
def hopfResidueTheta : IntegerSeries :=
  residueEvaluate (quarterSquareTheta 0) (quarterSquareTheta 1)
    (quarterSquareTheta 2) hopfSourceResiduePolynomial

def ambientOddFourSquareTheta : IntegerSeries :=
  residueEvaluate (quarterSquareTheta 0) (quarterSquareTheta 1)
    (quarterSquareTheta 2) oddFourSquareResiduePolynomial

/-- The surviving signed current after subtracting the ambient four-square
body from twice the Hopf-admitted body. -/
def hopfHeckeThetaCurrent : IntegerSeries :=
  8 * quarterSquareTheta 1 *
    (quarterSquareTheta 0 + quarterSquareTheta 2) *
    (quarterSquareTheta 0 - quarterSquareTheta 2) ^ 2

/-- **THE FINITE CENSUS LIFTS EXACTLY TO THE THETA BODY.** -/
theorem hopfResidueTheta_difference :
    2 * hopfResidueTheta - ambientOddFourSquareTheta =
      hopfHeckeThetaCurrent := by
  exact residueEvaluate_hopfDifference
    (quarterSquareTheta 0) (quarterSquareTheta 1) (quarterSquareTheta 2)

#print axioms quarterSquarePopulation_one_card_eq_three
#print axioms quarterSquareTheta_one_eq_three
#print axioms hopfResidueTheta_difference

end Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
