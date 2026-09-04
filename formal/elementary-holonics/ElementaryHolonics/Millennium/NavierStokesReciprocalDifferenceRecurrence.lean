import ElementaryHolonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
import ElementaryHolonics.Foundation.HigherDifferenceTransport

/-!
# The quadratic Hodge specialization of higher-difference transport

**[proved-derived]** The annular Hodge multiplier is a quadratic numerator times the reciprocal of
the genuine quadratic frequency denominator.  The reusable product and reciprocal calculus is
owned by `Foundation.HigherDifferenceTransport`; this file supplies the spatial-frequency
transports, proves the quadratic annihilator faces, and applies the order-six recurrence to the
actual Hodge reciprocal.

The theorem is local to the seven-point addressed window.  It does not assume that the totalized
Hodge reciprocal is globally inverse at the zero frequency.
-/

noncomputable section

open scoped BigOperators fwdDiff

namespace Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.HigherDifferenceTransport

/-! ## The actual annular Hodge denominator on one coordinate path -/

/-- The genuine quadratic frequency denominator along an addressed coordinate ray. -/
def hodgeDenominatorPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ) : ℂ :=
  (frequencySquared (frequency + offset • coordinateStep axis) : ℝ)

/-- The actual totalized Hodge reciprocal along the same addressed ray. -/
def hodgeReciprocalPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ) : ℂ :=
  hodgeReciprocal (frequency + offset • coordinateStep axis)

/-- The coordinate restriction of the genuine frequency denominator is exactly quadratic. -/
theorem hodgeDenominatorPath_thirdDifference_eq_zero
    (axis : Fin 3) (frequency : SpatialFrequency) :
    (fwdDiff 1)^[3] (hodgeDenominatorPath axis frequency) = 0 := by
  funext offset
  fin_cases axis <;>
    simp [hodgeDenominatorPath, fwdDiff, coordinateStep, frequencySquared,
      Fin.sum_univ_succ] <;> ring

/-- Away from the zero frequency, the genuine denominator and the totalized Hodge reciprocal are
actual inverses at the addressed path occurrence. -/
theorem hodgeDenominatorPath_mul_hodgeReciprocalPath
    (axis : Fin 3) (frequency : SpatialFrequency) (offset : ℕ)
    (hnonzero : frequencySquared (frequency + offset • coordinateStep axis) ≠ 0) :
    hodgeDenominatorPath axis frequency offset *
        hodgeReciprocalPath axis frequency offset = 1 := by
  have hcomplex :
      ((frequencySquared (frequency + offset • coordinateStep axis) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hnonzero
  unfold hodgeDenominatorPath hodgeReciprocalPath hodgeReciprocal
  rw [one_div]
  exact mul_inv_cancel₀ hcomplex

/-- The order-six reciprocal recurrence now applies to the actual Hodge denominator on every
seven-point annular coordinate window that stays away from zero. -/
theorem hodgeReciprocalPath_sixthDifference_recurrence
    (axis : Fin 3) (frequency : SpatialFrequency)
    (hnonzero : ∀ offset ≤ 6,
      frequencySquared (frequency + offset • coordinateStep axis) ≠ 0) :
    hodgeDenominatorPath axis frequency 0 *
        (fwdDiff 1)^[6] (hodgeReciprocalPath axis frequency) 0 =
      -(6 * fwdDiff 1 (hodgeDenominatorPath axis frequency) 0 *
          (fwdDiff 1)^[5] (hodgeReciprocalPath axis frequency) 1 +
        15 * (fwdDiff 1)^[2] (hodgeDenominatorPath axis frequency) 0 *
          (fwdDiff 1)^[4] (hodgeReciprocalPath axis frequency) 2) := by
  apply quadraticReciprocal_sixthDifference_recurrence
  · intro offset hoff
    simpa using hodgeDenominatorPath_mul_hodgeReciprocalPath
      axis frequency offset (hnonzero offset hoff)
  · exact hodgeDenominatorPath_thirdDifference_eq_zero axis frequency

/-! ## The three-axis order-six stencil has a sparse quadratic denominator face -/

/-- The genuine addressed coordinate translations consumed by the generic higher-difference
owner. -/
def coordinateTransport (axis : Fin 3) (frequency : SpatialFrequency) : SpatialFrequency :=
  frequency + coordinateStep axis

/-- Coordinate translation supplies an exact interchange receipt. -/
theorem coordinateTransport_interchange : InterchangeReceipt coordinateTransport := by
  intro first second frequency
  simp only [coordinateTransport]
  abel

/-- Two differences in each of the three lattice directions, retained as one addressed word. -/
def secondEachAxisWord : List (Fin 3) := [0, 0, 1, 1, 2, 2]

theorem secondEachAxisWord_length : secondEachAxisWord.length = 6 := by
  decide

/-- Before the commuting quotient, the six addressed occurrences return all sixty-four binary
product faces. -/
theorem secondEachAxis_productLedger_length
    (left right : SpatialFrequency → ℂ) :
    (productLedger coordinateTransport secondEachAxisWord left right).length = 64 := by
  rw [productLedger_length, secondEachAxisWord_length]
  norm_num

/-- Every one of the sixty-four occurrence leaves is transported into the twenty-seven-face
commuting `(2,2,2)` allocation receiver.  Multiplicity is retained by the list. -/
def secondEachAxisAllocationLedger (left right : SpatialFrequency → ℂ) :
    List ThreeAxisSecondOrderAllocation :=
  (productLedger coordinateTransport secondEachAxisWord left right).map
    secondOrderAllocationReceiver

theorem secondEachAxisAllocationLedger_length
    (left right : SpatialFrequency → ℂ) :
    (secondEachAxisAllocationLedger left right).length = 64 := by
  simp [secondEachAxisAllocationLedger, secondEachAxis_productLedger_length]

theorem secondEachAxisAllocation_receiver_card :
    Fintype.card ThreeAxisSecondOrderAllocation = 27 :=
  threeAxisSecondOrderAllocation_card

/-- The generic local reciprocal recurrence specializes to the genuine quadratic Hodge
denominator on the complete three-axis successor population. -/
theorem hodgeReciprocal_secondEachAxis_localRecurrence
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport secondEachAxisWord frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency =
      -ledgerSum
        (reciprocalRemainderLedger coordinateTransport secondEachAxisWord
          (fun current ↦ (frequencySquared current : ℂ)) hodgeReciprocal) frequency := by
  refine localReciprocal_recurrence coordinateTransport secondEachAxisWord
    (fun current ↦ (frequencySquared current : ℂ)) hodgeReciprocal frequency (by decide) ?_
  intro current hcurrent
  have hcomplex : ((frequencySquared current : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hnonzero current hcurrent)
  simp only [hodgeReciprocal, one_div]
  exact mul_inv_cancel₀ hcomplex

/-- Permuting the six coordinate occurrences does not change the returned Hodge reciprocal
difference, because the coordinate transports carry the exact interchange receipt above. -/
theorem hodgeReciprocal_secondEachAxis_permutationInvariant
    {word : List (Fin 3)} (permutation : word.Perm secondEachAxisWord) :
    differenceWord coordinateTransport word hodgeReciprocal =
      differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal :=
  differenceWord_eq_of_perm coordinateTransport coordinateTransport_interchange permutation _

/-- Iterated forward differences in all three genuine lattice coordinates. -/
def threeAxisMixedForwardDifference
    (first second third : Fin 3)
    (firstOrder secondOrder thirdOrder : ℕ)
    (coefficient : SpatialFrequency → ℂ) : SpatialFrequency → ℂ :=
  (fwdDiff (coordinateStep first))^[firstOrder]
    ((fwdDiff (coordinateStep second))^[secondOrder]
      ((fwdDiff (coordinateStep third))^[thirdOrder] coefficient))

/-- The seven possible nonzero denominator faces: its value, one first difference in any of three
coordinates, or one same-coordinate second difference. -/
inductive QuadraticDenominatorFace
  | value
  | first (axis : Fin 3)
  | second (axis : Fin 3)
  deriving DecidableEq, Fintype

/-- The separable quadratic denominator has exactly seven candidate faces before any product
estimate is taken. -/
theorem quadraticDenominatorFace_card : Fintype.card QuadraticDenominatorFace = 7 := by
  native_decide

/-- Cross-coordinate first differences of the genuine frequency denominator vanish exactly. -/
theorem frequencySquared_crossDifference_eq_zero
    (first second : Fin 3) (haxes : first ≠ second)
    (frequency : SpatialFrequency) :
    fwdDiff (coordinateStep first)
      (fwdDiff (coordinateStep second)
        (fun current ↦ (frequencySquared current : ℂ))) frequency = 0 := by
  fin_cases first <;> fin_cases second <;>
    simp_all [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- Every same-coordinate second difference of the genuine frequency denominator is exactly two. -/
theorem frequencySquared_sameAxis_secondDifference_eq_two
    (axis : Fin 3) (frequency : SpatialFrequency) :
    (fwdDiff (coordinateStep axis))^[2]
      (fun current ↦ (frequencySquared current : ℂ)) frequency = 2 := by
  fin_cases axis <;>
    simp [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ] <;>
    ring

/-- Every same-coordinate third denominator difference vanishes. -/
theorem frequencySquared_sameAxis_thirdDifference_eq_zero
    (axis : Fin 3) :
    (fwdDiff (coordinateStep axis))^[3]
      (fun current ↦ (frequencySquared current : ℂ)) = 0 := by
  funext frequency
  fin_cases axis <;>
    simp [fwdDiff, coordinateStep, frequencySquared, Fin.sum_univ_succ] <;>
    ring

end Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.hodgeReciprocalPath_sixthDifference_recurrence
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.hodgeReciprocal_secondEachAxis_localRecurrence
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.hodgeReciprocal_secondEachAxis_permutationInvariant
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.frequencySquared_crossDifference_eq_zero
#print axioms Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence.frequencySquared_sameAxis_thirdDifference_eq_zero
