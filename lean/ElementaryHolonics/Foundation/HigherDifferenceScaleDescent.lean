import ElementaryHolonics.Foundation.HigherDifferenceAnnihilator
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Strict scale descent for higher-difference ledgers

An annihilator-pruned recurrence is useful only when every retained face points to a strict
predecessor order.  This owner records that address, the transported successor receiver, the
occurrence multiplicity, the coefficient, and the lower-order section together.  Its norm theorem
returns the complete weighted predecessor envelope without replacing the face population by an
untyped constant.
-/

noncomputable section

namespace Soma.Holonics.HigherDifferenceScaleDescent

open Soma.Holonics.HigherDifferenceTransport

universe u v w

/-- Under an interchange receipt, differentiating a transported section is the transported
difference.  This comparison square exposes the actual shifted predecessor receiver. -/
theorem difference_shift_of_interchange
    {Generator : Type u} {State : Type v} {R : Type w} [CommRing R]
    (transport : Generator → State → State)
    (hinterchange : InterchangeReceipt transport)
    (first second : Generator) (observable : State → R) :
    difference transport first (shift transport second observable) =
      shift transport second (difference transport first observable) := by
  funext state
  simp only [difference, shift]
  rw [hinterchange first second state]

/-- One retained recurrence face addressed to a strict predecessor of `order`.  `multiplicity`
retains how many occurrence faces entered the grouped coefficient; it is testimony and is not
silently coerced into the returned value. -/
structure StrictOrderFace (State : Type v) (R : Type w) (order : ℕ) where
  predecessor : Fin order
  successor : State
  multiplicity : ℕ
  coefficient : R
  lowerSection : State → R

namespace StrictOrderFace

/-- The exact value returned by one grouped predecessor face. -/
def value [Mul R] {order : ℕ} (face : StrictOrderFace State R order) : R :=
  face.coefficient * face.lowerSection face.successor

theorem predecessor_lt {order : ℕ} (face : StrictOrderFace State R order) :
    face.predecessor.val < order :=
  face.predecessor.isLt

end StrictOrderFace

/-- Sum the complete strict-predecessor population. -/
def strictOrderReturn [AddMonoid R] [Mul R] {order : ℕ}
    (ledger : List (StrictOrderFace State R order)) : R :=
  (ledger.map StrictOrderFace.value).sum

/-- The real envelope returned by the same addressed predecessor population. -/
def strictOrderEnvelope {order : ℕ}
    (ledger : List (StrictOrderFace State R order))
    (coefficientEnvelope : StrictOrderFace State R order → ℝ)
    (lowerEnvelope : Fin order → ℝ) : ℝ :=
  (ledger.map fun face ↦ coefficientEnvelope face * lowerEnvelope face.predecessor).sum

/-- Exact triangle descent: coefficient and lower-section bounds on every retained face control
the complete return by the addressed strict-order envelope. -/
theorem norm_strictOrderReturn_le_envelope [NormedRing R]
    {order : ℕ} (ledger : List (StrictOrderFace State R order))
    (coefficientEnvelope : StrictOrderFace State R order → ℝ)
    (lowerEnvelope : Fin order → ℝ)
    (coefficientNonnegative : ∀ face ∈ ledger, 0 ≤ coefficientEnvelope face)
    (lowerNonnegative : ∀ face ∈ ledger, 0 ≤ lowerEnvelope face.predecessor)
    (coefficientBound : ∀ face ∈ ledger, ‖face.coefficient‖ ≤ coefficientEnvelope face)
    (lowerBound : ∀ face ∈ ledger,
      ‖face.lowerSection face.successor‖ ≤ lowerEnvelope face.predecessor) :
    ‖strictOrderReturn ledger‖ ≤
      strictOrderEnvelope ledger coefficientEnvelope lowerEnvelope := by
  induction ledger with
  | nil => simp [strictOrderReturn, strictOrderEnvelope]
  | cons face ledger ih =>
      have hcoefficient : ‖face.coefficient‖ ≤ coefficientEnvelope face :=
        coefficientBound face (by simp)
      have hlower : ‖face.lowerSection face.successor‖ ≤
          lowerEnvelope face.predecessor :=
        lowerBound face (by simp)
      have hcoefficientNonnegative : 0 ≤ coefficientEnvelope face :=
        coefficientNonnegative face (by simp)
      have hlowerNonnegative : 0 ≤ lowerEnvelope face.predecessor :=
        lowerNonnegative face (by simp)
      have ih' := ih
        (fun current hcurrent ↦ coefficientNonnegative current (by simp [hcurrent]))
        (fun current hcurrent ↦ lowerNonnegative current (by simp [hcurrent]))
        (fun current hcurrent ↦ coefficientBound current (by simp [hcurrent]))
        (fun current hcurrent ↦ lowerBound current (by simp [hcurrent]))
      simp only [strictOrderReturn, strictOrderEnvelope, List.map_cons, List.sum_cons,
        StrictOrderFace.value]
      calc
        ‖face.coefficient * face.lowerSection face.successor +
            (ledger.map StrictOrderFace.value).sum‖ ≤
          ‖face.coefficient * face.lowerSection face.successor‖ +
            ‖(ledger.map StrictOrderFace.value).sum‖ := norm_add_le _ _
        _ ≤ coefficientEnvelope face * lowerEnvelope face.predecessor +
            (ledger.map fun current ↦
              coefficientEnvelope current * lowerEnvelope current.predecessor).sum := by
          apply add_le_add
          · exact (norm_mul_le _ _).trans
              (mul_le_mul hcoefficient hlower (norm_nonneg _)
                hcoefficientNonnegative)
          · exact ih'

end Soma.Holonics.HigherDifferenceScaleDescent

section Audit
open Soma.Holonics.HigherDifferenceScaleDescent
#print axioms difference_shift_of_interchange
#print axioms StrictOrderFace.predecessor_lt
#print axioms norm_strictOrderReturn_le_envelope
end Audit
