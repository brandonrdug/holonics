import ElementaryHolonics.Foundation.HigherDifferenceAnnihilator
import ElementaryHolonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

/-!
# The quadratic Hodge denominator prunes the complete reciprocal ledger

The six-occurrence HD0 remainder has sixty-three raw faces.  This client retains a face exactly
when the quadratic denominator receives one difference, or two differences in the same coordinate.
Every other face is removed only after its left section is proved identically zero.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesQuadraticAnnihilatorLedger

open Soma.Holonics.HigherDifferenceTransport
open Soma.Holonics.HigherDifferenceAnnihilator
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeHigherMixedVariation
open Soma.Holonics.Millennium.NavierStokesReciprocalDifferenceRecurrence

/-- The complete nonprincipal reciprocal remainder for the genuine quadratic Hodge denominator. -/
def hodgeQuadraticRemainderLedger :
    List (ProductFace (Fin 3) SpatialFrequency ℂ) :=
  reciprocalRemainderLedger coordinateTransport secondEachAxisWord
    (fun frequency ↦ (frequencySquared frequency : ℂ)) hodgeReciprocal

theorem hodgeQuadraticRemainderLedger_length : hodgeQuadraticRemainderLedger.length = 63 := by
  rfl

/-- The coordinate addresses at which one face differentiates the denominator. -/
def denominatorDifferenceAxes (face : ProductFace (Fin 3) SpatialFrequency ℂ) : List (Fin 3) :=
  (face.trail.filter fun occurrence ↦ decide (occurrence.2 = .left)).map Prod.fst

/-- A separable quadratic denominator can retain one difference, or two differences in the same
coordinate.  The empty case is the principal face, which is not in the remainder ledger. -/
def quadraticDenominatorActive (face : ProductFace (Fin 3) SpatialFrequency ℂ) : Bool :=
  match denominatorDifferenceAxes face with
  | [_] => true
  | [first, second] => decide (first = second)
  | _ => false

/-- Every face rejected by the quadratic support receiver has exactly zero returned value. -/
theorem hodgeQuadraticRemainder_zero_of_inactive
    (frequency : SpatialFrequency) :
    ∀ face ∈ hodgeQuadraticRemainderLedger,
      quadraticDenominatorActive face = false → face.value frequency = 0 := by
  simp [hodgeQuadraticRemainderLedger, secondEachAxisWord, reciprocalRemainderLedger,
    principalFace, expandFace, rightBranch, leftBranch, denominatorDifferenceAxes,
    quadraticDenominatorActive, ProductFace.value, difference, shift, coordinateTransport,
    coordinateStep, frequencySquared, Fin.sum_univ_succ]

/-- The proof-bearing HD1 annihilator certificate at one frequency receiver. -/
def hodgeQuadraticAnnihilatorCertificate (frequency : SpatialFrequency) :
    AnnihilatorCertificate hodgeQuadraticRemainderLedger frequency where
  active := quadraticDenominatorActive
  zero_of_inactive := hodgeQuadraticRemainder_zero_of_inactive frequency

/-- The sixty-three raw remainder faces prune to nine occurrence-level active faces: six first
differences and three same-coordinate second differences. -/
theorem hodgeQuadratic_activeLedger_length (frequency : SpatialFrequency) :
    (hodgeQuadraticAnnihilatorCertificate frequency).activeLedger.length = 9 := by
  change (hodgeQuadraticRemainderLedger.filter quadraticDenominatorActive).length = 9
  rfl

/-- Fifty-four raw faces carry a cross-axis or order-at-least-three denominator difference and are
returned separately as the annihilated population. -/
theorem hodgeQuadratic_annihilatedLedger_length (frequency : SpatialFrequency) :
    (hodgeQuadraticAnnihilatorCertificate frequency).annihilatedLedger.length = 54 := by
  change
    (hodgeQuadraticRemainderLedger.filter fun face ↦ !quadraticDenominatorActive face).length = 54
  rfl

/-- The pruned nine-face occurrence sum is exactly the complete sixty-three-face remainder sum. -/
theorem hodgeQuadratic_ledgerSum_eq_activeLedger (frequency : SpatialFrequency) :
    ledgerSum hodgeQuadraticRemainderLedger frequency =
      ledgerSum (hodgeQuadraticAnnihilatorCertificate frequency).activeLedger frequency :=
  ledgerSum_eq_activeLedger (hodgeQuadraticAnnihilatorCertificate frequency)

/-- The local Hodge reciprocal recurrence now returns only its nine active occurrence faces. -/
theorem hodgeReciprocal_secondEachAxis_activeRecurrence
    (frequency : SpatialFrequency)
    (hnonzero : ∀ current ∈ successorWindow coordinateTransport secondEachAxisWord frequency,
      frequencySquared current ≠ 0) :
    (frequencySquared frequency : ℂ) *
        differenceWord coordinateTransport secondEachAxisWord hodgeReciprocal frequency =
      -ledgerSum (hodgeQuadraticAnnihilatorCertificate frequency).activeLedger frequency := by
  rw [← hodgeQuadratic_ledgerSum_eq_activeLedger]
  exact hodgeReciprocal_secondEachAxis_localRecurrence frequency hnonzero

/-- A uniform bound on each of the nine active occurrences controls the complete reciprocal
remainder with the exact active multiplicity. -/
theorem norm_hodgeQuadraticRemainder_le_nine_mul
    (frequency : SpatialFrequency) (bound : ℝ)
    (faceBound : ∀ face ∈ (hodgeQuadraticAnnihilatorCertificate frequency).activeLedger,
      ‖face.value frequency‖ ≤ bound) :
    ‖ledgerSum hodgeQuadraticRemainderLedger frequency‖ ≤ 9 * bound := by
  have hbound := norm_ledgerSum_le_activeLength_mul
    (hodgeQuadraticAnnihilatorCertificate frequency) bound faceBound
  rw [hodgeQuadratic_activeLedger_length] at hbound
  norm_num at hbound ⊢
  exact hbound

end Soma.Holonics.Millennium.NavierStokesQuadraticAnnihilatorLedger

section Audit
open Soma.Holonics.Millennium.NavierStokesQuadraticAnnihilatorLedger
#print axioms hodgeQuadraticRemainder_zero_of_inactive
#print axioms hodgeQuadratic_activeLedger_length
#print axioms hodgeQuadratic_annihilatedLedger_length
#print axioms hodgeQuadratic_ledgerSum_eq_activeLedger
#print axioms hodgeReciprocal_secondEachAxis_activeRecurrence
#print axioms norm_hodgeQuadraticRemainder_le_nine_mul
end Audit
