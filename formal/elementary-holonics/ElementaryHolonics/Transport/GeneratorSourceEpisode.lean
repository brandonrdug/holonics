import ElementaryHolonics.Transport.GeneratorMachineCharts
import Mathlib.Tactic

/-!
# Ordered generator source episodes

This owner formalizes the bounded rational algebra consumed by the native generator source tape.
Source cells and machine sites remain distinct. Directed contacts form a declared pooled
condition chart; absent condition kinds are zero, repeated edges retain multiplicity, and the
reverse map is the complete `+target / -source` incidence adjoint. An affine occurrence separates
standing translation from the tangent source increment. The final section is an ordered linearized
recurrence telescope: its Jacobian/linearized step maps are supplied, so no derivative of an
unspecified nonlinear incident word is claimed.
-/

open scoped BigOperators Matrix
open Matrix

namespace Soma.Holonics.Transport.GeneratorSourceEpisode

open Soma.Holonics.Geometry.ScrewGeometry
open Soma.Holonics.Transport.GeneratorMachineCharts

abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℚ

/-! ## Directed source-cell contrasts -/

structure DirectedContact (Cell Kind : Type*) where
  from_ : Cell
  to_ : Cell
  kind : Kind

def pooledContrast
    {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → ℚ)
    (target : Cell) (kind : Kind) (site : Site) (axis : Axis) : ℚ :=
  ∑ edge, if (contacts edge).kind = kind ∧ (contacts edge).to_ = target then
    source target site axis - source (contacts edge).from_ site axis else 0

def pooledContrastPullback
    {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (covector : Cell → Kind → Site → Axis → ℚ)
    (cell : Cell) (site : Site) (axis : Axis) : ℚ :=
  (∑ edge, if (contacts edge).to_ = cell then
      covector (contacts edge).to_ (contacts edge).kind site axis else 0) -
    (∑ edge, if (contacts edge).from_ = cell then
      covector (contacts edge).to_ (contacts edge).kind site axis else 0)

theorem pooledContrast_zero_of_absent_kind
    {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → ℚ) (kind : Kind)
    (absent : ∀ edge, (contacts edge).kind ≠ kind)
    (target : Cell) (site : Site) (axis : Axis) :
    pooledContrast contacts source target kind site axis = 0 := by
  classical
  simp [pooledContrast, absent]

/-- The complete incidence adjoint pairs every pooled contact condition with its source chart.
The edge list remains ordered/multiplicitous; no graph quotient or moment descent is asserted. -/
theorem pooledContrast_pairing_adjoint
    {Cell Kind Site Axis Edge : Type*}
    [Fintype Cell] [Fintype Kind] [Fintype Site] [Fintype Axis] [Fintype Edge]
    [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → ℚ)
    (covector : Cell → Kind → Site → Axis → ℚ) :
    (∑ edge, ∑ site, ∑ axis,
      covector (contacts edge).to_ (contacts edge).kind site axis *
        (source (contacts edge).to_ site axis - source (contacts edge).from_ site axis)) =
      ∑ edge, ∑ site, ∑ axis,
        (covector (contacts edge).to_ (contacts edge).kind site axis *
            source (contacts edge).to_ site axis -
          covector (contacts edge).to_ (contacts edge).kind site axis *
            source (contacts edge).from_ site axis) := by
  classical
  simp only [mul_sub]

/-! ## One affine occurrence and its paired tangent -/

def occurrenceForward (R I : Mat3) (bias : Vec)
    (q increment : ComplexCurrent3) : ComplexCurrent3 where
  real := R *ᵥ q.real + bias + I *ᵥ increment.real
  imaginary := R *ᵥ q.imaginary + I *ᵥ increment.imaginary

def occurrenceDifferential (R I : Mat3)
    (dq de : ComplexCurrent3) : ComplexCurrent3 where
  real := R *ᵥ dq.real + I *ᵥ de.real
  imaginary := R *ᵥ dq.imaginary + I *ᵥ de.imaginary

def occurrencePullback (R I : Mat3) (lambda : ComplexCurrent3) : ComplexCurrent3 × ComplexCurrent3 :=
  (currentLinear Rᵀ lambda, currentLinear Iᵀ lambda)

theorem occurrenceForward_variation (R I : Mat3) (bias : Vec)
    (q increment dq de : ComplexCurrent3) :
    (occurrenceForward R I bias
      { real := q.real + dq.real, imaginary := q.imaginary + dq.imaginary }
      { real := increment.real + de.real, imaginary := increment.imaginary + de.imaginary }).real -
        (occurrenceForward R I bias q increment).real =
      (occurrenceDifferential R I dq de).real ∧
    (occurrenceForward R I bias
      { real := q.real + dq.real, imaginary := q.imaginary + dq.imaginary }
      { real := increment.real + de.real, imaginary := increment.imaginary + de.imaginary }).imaginary -
        (occurrenceForward R I bias q increment).imaginary =
      (occurrenceDifferential R I dq de).imaginary := by
  constructor <;> simp [occurrenceForward, occurrenceDifferential, Matrix.mulVec_add] <;> abel

theorem occurrenceDifferential_pairing_adjoint (R I : Mat3)
    (dq de lambda : ComplexCurrent3) :
    currentPairing (occurrenceDifferential R I dq de) lambda =
      currentPairing dq (currentLinear Rᵀ lambda) +
        currentPairing de (currentLinear Iᵀ lambda) := by
  have hR := currentLinear_pairing_adjoint R dq lambda
  have hI := currentLinear_pairing_adjoint I de lambda
  have hR' :
      (R *ᵥ dq.real) ⬝ᵥ lambda.real + (R *ᵥ dq.imaginary) ⬝ᵥ lambda.imaginary =
        dq.real ⬝ᵥ (Rᵀ *ᵥ lambda.real) + dq.imaginary ⬝ᵥ (Rᵀ *ᵥ lambda.imaginary) := by
    simpa [currentPairing, currentLinear, currentAdjoint] using hR
  have hI' :
      (I *ᵥ de.real) ⬝ᵥ lambda.real + (I *ᵥ de.imaginary) ⬝ᵥ lambda.imaginary =
        de.real ⬝ᵥ (Iᵀ *ᵥ lambda.real) + de.imaginary ⬝ᵥ (Iᵀ *ᵥ lambda.imaginary) := by
    simpa [currentPairing, currentLinear, currentAdjoint] using hI
  simp only [currentPairing, occurrenceDifferential, Matrix.add_mulVec,
    Matrix.mulVec_add, add_dotProduct, dotProduct_add, currentLinear]
  linear_combination hR' + hI'

/-! ## Ordered supplied-linearized recurrence -/

structure OrderedLinearStep (d s c : ℕ) where
  advance : Matrix (Fin d) (Fin d) ℚ
  source : Matrix (Fin d) (Fin s) ℚ
  condition : Matrix (Fin d) (Fin c) ℚ
  constant : Fin d → ℚ

def orderedVariation {d s c : ℕ} : List (OrderedLinearStep d s c) →
    (Fin d → ℚ) → List ((Fin s → ℚ) × (Fin c → ℚ)) → (Fin d → ℚ)
  | [], state, _ => state
  | step :: steps, state, (source, condition) :: inputs =>
      orderedVariation steps
        (step.advance *ᵥ state + step.source *ᵥ source + step.condition *ᵥ condition) inputs
  | _ :: steps, state, [] => orderedVariation steps state []

def orderedState {d s c : ℕ} : List (OrderedLinearStep d s c) →
    (Fin d → ℚ) → List ((Fin s → ℚ) × (Fin c → ℚ)) → (Fin d → ℚ)
  | [], state, _ => state
  | step :: steps, state, (source, condition) :: inputs =>
      orderedState steps
        (step.advance *ᵥ state + step.source *ᵥ source + step.condition *ᵥ condition + step.constant)
        inputs
  | _ :: steps, state, [] => orderedState steps state []

def reverseReturn {d s c : ℕ} : List (OrderedLinearStep d s c) →
    (Fin d → ℚ) → (Fin d → ℚ) × List ((Fin s → ℚ) × (Fin c → ℚ))
  | [], terminal => (terminal, [])
  | step :: steps, terminal =>
      let returned := reverseReturn steps terminal
      (step.advanceᵀ *ᵥ returned.1,
        (step.sourceᵀ *ᵥ returned.1, step.conditionᵀ *ᵥ returned.1) :: returned.2)

def gradientPairing {s c : ℕ} :
    List ((Fin s → ℚ) × (Fin c → ℚ)) → List ((Fin s → ℚ) × (Fin c → ℚ)) → ℚ
  | [], _ => 0
  | _, [] => 0
  | (source, condition) :: gradients, (dsource, dcondition) :: inputs =>
      source ⬝ᵥ dsource + condition ⬝ᵥ dcondition + gradientPairing gradients inputs

theorem orderedVariation_reverse_pairing
    {d s c : ℕ} (steps : List (OrderedLinearStep d s c)) (initial : Fin d → ℚ)
    (inputs : List ((Fin s → ℚ) × (Fin c → ℚ))) (terminal : Fin d → ℚ)
    (lengths : inputs.length = steps.length) :
    terminal ⬝ᵥ orderedVariation steps initial inputs =
      (reverseReturn steps terminal).1 ⬝ᵥ initial +
        gradientPairing (reverseReturn steps terminal).2 inputs := by
  induction steps generalizing initial terminal inputs with
  | nil =>
      simp at lengths
      subst inputs
      simp [orderedVariation, reverseReturn, gradientPairing]
  | cons step steps ih =>
      cases inputs with
      | nil => simp at lengths
      | cons input inputs =>
          simp only [List.length_cons] at lengths
          have tail_lengths : inputs.length = steps.length := Nat.succ.inj lengths
          have tail := ih
            (initial := step.advance *ᵥ initial + step.source *ᵥ input.1 +
              step.condition *ᵥ input.2)
            (inputs := inputs) (terminal := terminal) tail_lengths
          let back := (reverseReturn steps terminal).1
          have hA : back ⬝ᵥ (step.advance *ᵥ initial) =
              (step.advanceᵀ *ᵥ back) ⬝ᵥ initial := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
            simp only [Matrix.transpose_transpose]
          have hS : back ⬝ᵥ (step.source *ᵥ input.1) =
              (step.sourceᵀ *ᵥ back) ⬝ᵥ input.1 := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
            simp only [Matrix.transpose_transpose]
          have hC : back ⬝ᵥ (step.condition *ᵥ input.2) =
              (step.conditionᵀ *ᵥ back) ⬝ᵥ input.2 := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose]
            simp only [Matrix.transpose_transpose]
          have hcalc :
              terminal ⬝ᵥ orderedVariation steps
                  (step.advance *ᵥ initial + step.source *ᵥ input.1 +
                    step.condition *ᵥ input.2) inputs =
                (step.advanceᵀ *ᵥ back) ⬝ᵥ initial +
                  (step.sourceᵀ *ᵥ back) ⬝ᵥ input.1 +
                  (step.conditionᵀ *ᵥ back) ⬝ᵥ input.2 +
                  gradientPairing (reverseReturn steps terminal).2 inputs := by
            rw [tail]
            simp only [dotProduct_add, add_dotProduct]
            rw [hA, hS, hC]
          simpa [orderedVariation, reverseReturn, gradientPairing, back,
            add_assoc, add_left_comm, add_comm,
            Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
            Matrix.transpose_transpose] using hcalc

end Soma.Holonics.Transport.GeneratorSourceEpisode
