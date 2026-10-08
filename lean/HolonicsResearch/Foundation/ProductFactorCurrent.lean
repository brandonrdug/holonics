import HolonicsResearch.Foundation.DiagonalChainTransport
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Factor and pair currents

The factor incidence and augmented contraction datum, exact pair current, and its left/right transports. The next axis boundary owner consumes these existing laws.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

/-! ## Factor currents and contractions -/

abbrev FactorSimplex (X : SSet) (degree : ℕ) := Simplex X degree
abbrev FactorCurrent (X : SSet) (degree : ℕ) := Current (FactorSimplex X degree)

def factorBoundaryAtom {X : SSet} {degree : ℕ}
    (simplex : FactorSimplex X (degree + 1)) : FactorCurrent X degree :=
  ∑ omitted : Fin (degree + 2), (-1 : ℚ) ^ (omitted : ℕ) •
    generator (face omitted simplex)

def factorBoundary (X : SSet) (degree : ℕ) :
    FactorCurrent X (degree + 1) →ₗ[ℚ] FactorCurrent X degree :=
  extend factorBoundaryAtom

@[simp]
theorem factorBoundary_generator {X : SSet} {degree : ℕ}
    (simplex : FactorSimplex X (degree + 1)) :
    factorBoundary X degree (generator simplex) = factorBoundaryAtom simplex := by
  exact extend_generator _ _

structure LowDegreeCurrentDatum (X : SSet) where
  basepoint : FactorSimplex X 0
  augmentation : FactorCurrent X 0 →ₗ[ℚ] ℚ
  augmentation_basepoint : augmentation (generator basepoint) = 1
  augmentation_boundary_zero : ∀ edge : FactorCurrent X 1,
    augmentation (factorBoundary X 0 edge) = 0
  boundary_boundary_zero : ∀ current : FactorCurrent X 2,
    factorBoundary X 0 (factorBoundary X 1 current) = 0
  h0 : FactorCurrent X 0 →ₗ[ℚ] FactorCurrent X 1
  h0_boundary : ∀ current,
    factorBoundary X 0 (h0 current) =
      current - augmentation current • generator basepoint
  h1 : FactorCurrent X 1 →ₗ[ℚ] FactorCurrent X 2
  h1_boundary_of_closed : ∀ (current : FactorCurrent X 1),
    factorBoundary X 0 current = 0 →
      factorBoundary X 1 (h1 current) = current

/-! The augmented degree-one contraction is defined on every edge current by first removing its
endpoint path.  The augmentation law makes this remainder closed. -/

def h1ClosedPart {X : SSet} (datum : LowDegreeCurrentDatum X)
    (current : FactorCurrent X 1) : FactorCurrent X 1 :=
  current - datum.h0 (factorBoundary X 0 current)

theorem h1ClosedPart_boundary_zero {X : SSet}
    (datum : LowDegreeCurrentDatum X) (current : FactorCurrent X 1) :
    factorBoundary X 0 (h1ClosedPart datum current) = 0 := by
  rw [h1ClosedPart, map_sub, datum.h0_boundary]
  rw [datum.augmentation_boundary_zero]
  simp

theorem h1ClosedPart_reconstruction {X : SSet}
    (datum : LowDegreeCurrentDatum X) (current : FactorCurrent X 1) :
    factorBoundary X 1 (datum.h1 (h1ClosedPart datum current)) =
      h1ClosedPart datum current := by
  exact datum.h1_boundary_of_closed _ (h1ClosedPart_boundary_zero datum current)

theorem h1_extended_boundary {X : SSet}
    (datum : LowDegreeCurrentDatum X) (current : FactorCurrent X 1) :
    factorBoundary X 1 (datum.h1 (h1ClosedPart datum current)) =
      current - datum.h0 (factorBoundary X 0 current) := by
  exact h1ClosedPart_reconstruction datum current

/-! ## Pair and axis currents -/

def pairCurrent {Left Right : Type*} (left : Current Left) (right : Current Right) :
    Current (Left × Right) :=
  finsuppTensorFinsupp' ℚ Left Right (left ⊗ₜ[ℚ] right)

@[simp]
theorem pairCurrent_generator {Left Right : Type*} (left : Left) (right : Right) :
    pairCurrent (generator left) (generator right) = generator (left, right) := by
  simp [pairCurrent, generator]

@[simp]
theorem pairCurrent_add_left {Left Right : Type*}
    (left₁ left₂ : Current Left) (right : Current Right) :
    pairCurrent (left₁ + left₂) right =
      pairCurrent left₁ right + pairCurrent left₂ right := by
  simp [pairCurrent, TensorProduct.add_tmul]

@[simp]
theorem pairCurrent_add_right {Left Right : Type*}
    (left : Current Left) (right₁ right₂ : Current Right) :
    pairCurrent left (right₁ + right₂) =
      pairCurrent left right₁ + pairCurrent left right₂ := by
  simp [pairCurrent, TensorProduct.tmul_add]

@[simp]
theorem pairCurrent_smul_left {Left Right : Type*}
    (q : ℚ) (left : Current Left) (right : Current Right) :
    pairCurrent (q • left) right = q • pairCurrent left right := by
  simp [pairCurrent, TensorProduct.smul_tmul]

@[simp]
theorem pairCurrent_smul_right {Left Right : Type*}
    (q : ℚ) (left : Current Left) (right : Current Right) :
    pairCurrent left (q • right) = q • pairCurrent left right := by
  simp [pairCurrent, TensorProduct.tmul_smul]

@[simp]
theorem pairCurrent_neg_left {Left Right : Type*}
    (left : Current Left) (right : Current Right) :
    pairCurrent (-left) right = -pairCurrent left right := by
  simpa only [neg_smul, one_smul] using
    pairCurrent_smul_left (Left := Left) (Right := Right) (-1) left right

@[simp]
theorem pairCurrent_neg_right {Left Right : Type*}
    (left : Current Left) (right : Current Right) :
    pairCurrent left (-right) = -pairCurrent left right := by
  simpa only [neg_smul, one_smul] using
    pairCurrent_smul_right (Left := Left) (Right := Right) (-1) left right

@[simp]
theorem pairCurrent_sub_left {Left Right : Type*}
    (left₁ left₂ : Current Left) (right : Current Right) :
    pairCurrent (left₁ - left₂) right =
      pairCurrent left₁ right - pairCurrent left₂ right := by
  rw [sub_eq_add_neg, pairCurrent_add_left, pairCurrent_neg_left, sub_eq_add_neg]

@[simp]
theorem pairCurrent_sub_right {Left Right : Type*}
    (left : Current Left) (right₁ right₂ : Current Right) :
    pairCurrent left (right₁ - right₂) =
      pairCurrent left right₁ - pairCurrent left right₂ := by
  rw [sub_eq_add_neg, pairCurrent_add_right, pairCurrent_neg_right, sub_eq_add_neg]

@[simp]
theorem pairCurrent_zero_left {Left Right : Type*} (right : Current Right) :
    pairCurrent (0 : Current Left) right = 0 := by
  simpa using pairCurrent_smul_left (Left := Left) (Right := Right) 0 0 right

@[simp]
theorem pairCurrent_zero_right {Left Right : Type*} (left : Current Left) :
    pairCurrent left (0 : Current Right) = 0 := by
  simpa using pairCurrent_smul_right (Left := Left) (Right := Right) 0 left 0

/-! Pair transport is one polarized operation.  Left and right are the two orientations of the
same exact incidence action; neither direction receives a separate constitutive law. -/

def mapPairLeft {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left') :
    Current (Left × Right) →ₗ[ℚ] Current (Left' × Right) :=
  extend fun pair => pairCurrent (transport (generator pair.1)) (generator pair.2)

def mapPairRight {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right') :
    Current (Left × Right) →ₗ[ℚ] Current (Left × Right') :=
  extend fun pair => pairCurrent (generator pair.1) (transport (generator pair.2))

@[simp]
theorem mapPairLeft_generator {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left') (left : Left) (right : Right) :
    mapPairLeft transport (generator (left, right)) =
      pairCurrent (transport (generator left)) (generator right) := by
  exact extend_generator _ _

@[simp]
theorem mapPairRight_generator {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right') (left : Left) (right : Right) :
    mapPairRight transport (generator (left, right)) =
      pairCurrent (generator left) (transport (generator right)) := by
  exact extend_generator _ _

theorem mapPairLeft_pairCurrent {Left Left' Right : Type*}
    (transport : Current Left →ₗ[ℚ] Current Left')
    (left : Current Left) (right : Current Right) :
    mapPairLeft transport (pairCurrent left right) =
      pairCurrent (transport left) right := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ h₁ h₂ =>
      simp only [pairCurrent_add_left, map_add, h₁, h₂]
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ h₁ h₂ =>
          simp only [pairCurrent_add_right, map_add, h₁, h₂]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, mapPairLeft_generator]

theorem mapPairRight_pairCurrent {Left Right Right' : Type*}
    (transport : Current Right →ₗ[ℚ] Current Right')
    (left : Current Left) (right : Current Right) :
    mapPairRight transport (pairCurrent left right) =
      pairCurrent left (transport right) := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ h₁ h₂ =>
      simp only [pairCurrent_add_left, map_add, h₁, h₂]
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ h₁ h₂ =>
          simp only [pairCurrent_add_right, map_add, h₁, h₂]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, mapPairRight_generator]

theorem mapPairLeft_comp {Left Middle Target Right : Type*}
    (outer : Current Middle →ₗ[ℚ] Current Target)
    (inner : Current Left →ₗ[ℚ] Current Middle)
    (current : Current (Left × Right)) :
    mapPairLeft outer (mapPairLeft inner current) =
      mapPairLeft (outer.comp inner) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator,
        mapPairLeft_pairCurrent, LinearMap.comp_apply]

theorem mapPairRight_comp {Left Right Middle Target : Type*}
    (outer : Current Middle →ₗ[ℚ] Current Target)
    (inner : Current Right →ₗ[ℚ] Current Middle)
    (current : Current (Left × Right)) :
    mapPairRight outer (mapPairRight inner current) =
      mapPairRight (outer.comp inner) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairRight_generator,
        mapPairRight_pairCurrent, LinearMap.comp_apply]

theorem mapPairLeft_right_commute
    {Left Left' Right Right' : Type*}
    (leftTransport : Current Left →ₗ[ℚ] Current Left')
    (rightTransport : Current Right →ₗ[ℚ] Current Right')
    (current : Current (Left × Right)) :
    mapPairLeft leftTransport (mapPairRight rightTransport current) =
      mapPairRight rightTransport (mapPairLeft leftTransport current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairRight_generator,
        mapPairLeft_pairCurrent, mapPairRight_pairCurrent]

/-- The datum's degree-one contraction extended from cycles to all edge currents. -/
def extendedH1 {X : SSet} (datum : LowDegreeCurrentDatum X) :
    FactorCurrent X 1 →ₗ[ℚ] FactorCurrent X 2 :=
  datum.h1.comp (LinearMap.id - datum.h0.comp (factorBoundary X 0))

theorem extendedH1_apply {X : SSet} (datum : LowDegreeCurrentDatum X)
    (current : FactorCurrent X 1) :
    extendedH1 datum current = datum.h1 (h1ClosedPart datum current) := by
  rfl

theorem extendedH1_boundary {X : SSet} (datum : LowDegreeCurrentDatum X)
    (current : FactorCurrent X 1) :
    factorBoundary X 1 (extendedH1 datum current) =
      current - datum.h0 (factorBoundary X 0 current) := by
  exact h1_extended_boundary datum current

section Audit

#print axioms factorBoundary_generator
#print axioms h1ClosedPart_boundary_zero
#print axioms h1ClosedPart_reconstruction
#print axioms h1_extended_boundary
#print axioms pairCurrent_generator
#print axioms pairCurrent_add_left
#print axioms pairCurrent_add_right
#print axioms pairCurrent_smul_left
#print axioms pairCurrent_smul_right
#print axioms pairCurrent_neg_left
#print axioms pairCurrent_neg_right
#print axioms pairCurrent_sub_left
#print axioms pairCurrent_sub_right
#print axioms pairCurrent_zero_left
#print axioms pairCurrent_zero_right
#print axioms mapPairLeft_generator
#print axioms mapPairRight_generator
#print axioms mapPairLeft_pairCurrent
#print axioms mapPairRight_pairCurrent
#print axioms mapPairLeft_comp
#print axioms mapPairRight_comp
#print axioms mapPairLeft_right_commute
#print axioms extendedH1_apply
#print axioms extendedH1_boundary

end Audit

end Holonics.DiagonalChainTransport
