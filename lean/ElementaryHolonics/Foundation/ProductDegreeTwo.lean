import ElementaryHolonics.Foundation.DiagonalChainTransport
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# A generic degree-two product current

This owner records the part of the low-degree product calculation which is independent of a
particular space.  The factor data supplies the two contraction passages actually used by the
calculation: an augmented degree-zero path and a degree-one filling on the closed kernel.  The
product return keeps all three degree-two axes and returns an addressed degree-three current.

The constructions below are deliberately current-level.  No Kunneth theorem, finite-dimensional
rank argument, or degree-two surjectivity is used.
-/

noncomputable section

namespace Soma.Holonics.DiagonalChainTransport

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

def leftAxis {X Y : SSet} :
    Current (FactorSimplex X 0 × FactorSimplex Y 2) →ₗ[ℚ]
      Current (TotalTwoOccurrence X Y) :=
  extend fun pair => generator (.left pair.1 pair.2)

def middleAxis {X Y : SSet} :
    Current (FactorSimplex X 1 × FactorSimplex Y 1) →ₗ[ℚ]
      Current (TotalTwoOccurrence X Y) :=
  extend fun pair => generator (.middle pair.1 pair.2)

def rightAxis {X Y : SSet} :
    Current (FactorSimplex X 2 × FactorSimplex Y 0) →ₗ[ℚ]
      Current (TotalTwoOccurrence X Y) :=
  extend fun pair => generator (.right pair.1 pair.2)

def leftMiddleAxis {X Y : SSet} :
    Current (FactorSimplex X 1 × FactorSimplex Y 2) →ₗ[ℚ]
      Current (TotalThreeOccurrence X Y) :=
  extend fun pair => generator (.leftMiddle pair.1 pair.2)

def rightMiddleAxis {X Y : SSet} :
    Current (FactorSimplex X 2 × FactorSimplex Y 1) →ₗ[ℚ]
      Current (TotalThreeOccurrence X Y) :=
  extend fun pair => generator (.rightMiddle pair.1 pair.2)

@[simp] theorem leftAxis_generator {X Y : SSet}
    (left : FactorSimplex X 0) (right : FactorSimplex Y 2) :
    leftAxis (generator (left, right)) = generator (.left left right) := by
  exact extend_generator _ _

@[simp] theorem middleAxis_generator {X Y : SSet}
    (left : FactorSimplex X 1) (right : FactorSimplex Y 1) :
    middleAxis (generator (left, right)) = generator (.middle left right) := by
  exact extend_generator _ _

@[simp] theorem rightAxis_generator {X Y : SSet}
    (left : FactorSimplex X 2) (right : FactorSimplex Y 0) :
    rightAxis (generator (left, right)) = generator (.right left right) := by
  exact extend_generator _ _

@[simp] theorem leftMiddleAxis_generator {X Y : SSet}
    (left : FactorSimplex X 1) (right : FactorSimplex Y 2) :
    leftMiddleAxis (generator (left, right)) = generator (.leftMiddle left right) := by
  exact extend_generator _ _

@[simp] theorem rightMiddleAxis_generator {X Y : SSet}
    (left : FactorSimplex X 2) (right : FactorSimplex Y 1) :
    rightMiddleAxis (generator (left, right)) = generator (.rightMiddle left right) := by
  exact extend_generator _ _

/-! The two degree-three polarized axes are one polarity family. -/

inductive MiddlePolarity | left | right

theorem totalBoundaryThree_rightMiddle_generator {X Y : SSet}
    (left : FactorSimplex X 2) (right : FactorSimplex Y 1) :
    totalBoundaryThree X Y (rightMiddleAxis (pairCurrent (generator left) (generator right))) =
      middleAxis (pairCurrent (factorBoundary X 1 (generator left)) (generator right)) +
        rightAxis (pairCurrent (generator left) (factorBoundary Y 0 (generator right))) := by
  simp only [pairCurrent_generator, rightMiddleAxis_generator,
    totalBoundaryThree, extend_generator, totalBoundaryThreeAtom,
    factorBoundary, factorBoundary_generator, factorBoundaryAtom]
  rw [Fin.sum_univ_three, Fin.sum_univ_two]
  norm_num
  abel

theorem totalBoundaryThree_leftMiddle_generator {X Y : SSet}
    (left : FactorSimplex X 1) (right : FactorSimplex Y 2) :
    totalBoundaryThree X Y (leftMiddleAxis (pairCurrent (generator left) (generator right))) =
      leftAxis (pairCurrent (factorBoundary X 0 (generator left)) (generator right)) -
        middleAxis (pairCurrent (generator left) (factorBoundary Y 1 (generator right))) := by
  simp only [pairCurrent_generator, leftMiddleAxis_generator,
    totalBoundaryThree, extend_generator, totalBoundaryThreeAtom,
    factorBoundary, factorBoundary_generator, factorBoundaryAtom]
  rw [Fin.sum_univ_two, Fin.sum_univ_three]
  norm_num
  abel

theorem totalBoundaryThree_rightMiddle {X Y : SSet}
    (left : FactorCurrent X 2) (right : FactorCurrent Y 1) :
    totalBoundaryThree X Y (rightMiddleAxis (pairCurrent left right)) =
      middleAxis (pairCurrent (factorBoundary X 1 left) right) +
        rightAxis (pairCurrent left (factorBoundary Y 0 right)) := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ h₁ h₂ =>
      simp only [pairCurrent_add_left, map_add, h₁, h₂]
      module
  | single leftSimplex coefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ h₁ h₂ =>
          simp only [pairCurrent_add_right, map_add, h₁, h₂]
          module
      | single rightSimplex coefficient' =>
          rw [show Finsupp.single leftSimplex coefficient =
              coefficient • generator leftSimplex by simp [generator],
            show Finsupp.single rightSimplex coefficient' =
              coefficient' • generator rightSimplex by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul]
          rw [totalBoundaryThree_rightMiddle_generator]
          module

theorem totalBoundaryThree_leftMiddle {X Y : SSet}
    (left : FactorCurrent X 1) (right : FactorCurrent Y 2) :
    totalBoundaryThree X Y (leftMiddleAxis (pairCurrent left right)) =
      leftAxis (pairCurrent (factorBoundary X 0 left) right) -
        middleAxis (pairCurrent left (factorBoundary Y 1 right)) := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ h₁ h₂ =>
      simp only [pairCurrent_add_left, map_add, h₁, h₂]
      module
  | single leftSimplex coefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ h₁ h₂ =>
          simp only [pairCurrent_add_right, map_add, h₁, h₂]
          module
      | single rightSimplex coefficient' =>
          rw [show Finsupp.single leftSimplex coefficient =
              coefficient • generator leftSimplex by simp [generator],
            show Finsupp.single rightSimplex coefficient' =
              coefficient' • generator rightSimplex by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul]
          rw [totalBoundaryThree_leftMiddle_generator]
          module

/-- [proved-derived; formal-checked] The right-middle Leibniz law on an arbitrary retained
occurrence population.  Closure is a property of the complete current, not of each generator. -/
theorem totalBoundaryThree_rightMiddleAxis {X Y : SSet}
    (current : Current (FactorSimplex X 2 × FactorSimplex Y 1)) :
    totalBoundaryThree X Y (rightMiddleAxis current) =
      middleAxis (mapPairLeft (factorBoundary X 1) current) +
        rightAxis (mapPairRight (factorBoundary Y 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairRight_generator]
      rw [show generator (leftOccurrence, rightOccurrence) =
          pairCurrent (generator leftOccurrence) (generator rightOccurrence) by
            rw [pairCurrent_generator]]
      rw [totalBoundaryThree_rightMiddle]
      module

/-- [proved-derived; formal-checked] The opposite polarized Leibniz law on the same complete
current semantics. -/
theorem totalBoundaryThree_leftMiddleAxis {X Y : SSet}
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 2)) :
    totalBoundaryThree X Y (leftMiddleAxis current) =
      leftAxis (mapPairLeft (factorBoundary X 0) current) -
        middleAxis (mapPairRight (factorBoundary Y 1) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairRight_generator]
      rw [show generator (leftOccurrence, rightOccurrence) =
          pairCurrent (generator leftOccurrence) (generator rightOccurrence) by
            rw [pairCurrent_generator]]
      rw [totalBoundaryThree_leftMiddle]
      module

theorem mapPairLeft_extendedH1_boundary {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × Right)) :
    mapPairLeft (factorBoundary X 1)
        (mapPairLeft (extendedH1 datum) current) =
      current -
        mapPairLeft datum.h0
          (mapPairLeft (factorBoundary X 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairLeft_pairCurrent,
        extendedH1_boundary]
      rw [pairCurrent_sub_left]
      simp only [pairCurrent_generator]
      module

theorem mapPairRight_extendedH1_boundary {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (Left × FactorSimplex Y 1)) :
    mapPairRight (factorBoundary Y 1)
        (mapPairRight (extendedH1 datum) current) =
      current -
        mapPairRight datum.h0
          (mapPairRight (factorBoundary Y 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨leftOccurrence, rightOccurrence⟩
      rw [show Finsupp.single (leftOccurrence, rightOccurrence) coefficient =
          coefficient • generator (leftOccurrence, rightOccurrence) by simp [generator]]
      simp only [map_smul, mapPairRight_generator, mapPairRight_pairCurrent,
        extendedH1_boundary]
      rw [pairCurrent_sub_right]
      simp only [pairCurrent_generator]
      module

/-! ## Complete-current polarized filling

The earlier generator theorem remains useful for decomposable cycles.  The construction below is
the required correction: its hypotheses concern the two boundary currents of the whole mixed
population, so cancellations between addressed occurrences remain visible. -/

def middleJointFillingLeft {X Y : SSet}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  rightMiddleAxis (mapPairLeft (extendedH1 datum) current)

def middleJointFillingRight {X Y : SSet}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  -leftMiddleAxis (mapPairRight (extendedH1 datum) current)

theorem boundary_middleJointFillingLeft {X Y : SSet}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1))
    (closedLeft : mapPairLeft (factorBoundary X 0) current = 0)
    (closedRight : mapPairRight (factorBoundary Y 0) current = 0) :
    totalBoundaryThree X Y (middleJointFillingLeft datum current) =
      middleAxis current := by
  rw [middleJointFillingLeft, totalBoundaryThree_rightMiddleAxis,
    mapPairLeft_extendedH1_boundary, closedLeft, map_zero, sub_zero]
  have commute := mapPairLeft_right_commute
    (extendedH1 datum) (factorBoundary Y 0) current
  rw [← commute, closedRight, map_zero, map_zero, add_zero]

theorem boundary_middleJointFillingRight {X Y : SSet}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1))
    (closedLeft : mapPairLeft (factorBoundary X 0) current = 0)
    (closedRight : mapPairRight (factorBoundary Y 0) current = 0) :
    totalBoundaryThree X Y (middleJointFillingRight datum current) =
      middleAxis current := by
  rw [middleJointFillingRight, map_neg, totalBoundaryThree_leftMiddleAxis,
    mapPairRight_extendedH1_boundary, closedRight, map_zero, sub_zero]
  have commute := mapPairLeft_right_commute
    (factorBoundary X 0) (extendedH1 datum) current
  rw [commute, closedLeft, map_zero, map_zero, zero_sub, neg_neg]

/-! ## Coupled-axis compression

The three degree-two axes are one current.  The projections below are lossless only as a family,
and closure returns two coupled equations.  This is the reusable local-to-global compression law:
the mixed axis is removed by one polarized degree-three current while its two returned differences
remain as separately closed outer currents. -/

def leftAxisProjection {X Y : SSet} :
    Current (TotalTwoOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 0 × FactorSimplex Y 2) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (left, right)
    | .middle _ _ => 0
    | .right _ _ => 0

def middleAxisProjection {X Y : SSet} :
    Current (TotalTwoOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 1 × FactorSimplex Y 1) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .middle left right => generator (left, right)
    | .right _ _ => 0

def rightAxisProjection {X Y : SSet} :
    Current (TotalTwoOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 2 × FactorSimplex Y 0) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .middle _ _ => 0
    | .right left right => generator (left, right)

def leftOneAxisProjection {X Y : SSet} :
    Current (TotalOneOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 0 × FactorSimplex Y 1) :=
  extend fun occurrence => match occurrence with
    | .left left right => generator (left, right)
    | .right _ _ => 0

def rightOneAxisProjection {X Y : SSet} :
    Current (TotalOneOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 1 × FactorSimplex Y 0) :=
  extend fun occurrence => match occurrence with
    | .left _ _ => 0
    | .right left right => generator (left, right)

def leftOneAxis {X Y : SSet} :
    Current (FactorSimplex X 0 × FactorSimplex Y 1) →ₗ[ℚ]
      Current (TotalOneOccurrence X Y) :=
  extend fun pair => generator (.left pair.1 pair.2)

def rightOneAxis {X Y : SSet} :
    Current (FactorSimplex X 1 × FactorSimplex Y 0) →ₗ[ℚ]
      Current (TotalOneOccurrence X Y) :=
  extend fun pair => generator (.right pair.1 pair.2)

@[simp] theorem leftOneAxis_generator {X Y : SSet}
    (left : FactorSimplex X 0) (right : FactorSimplex Y 1) :
    leftOneAxis (generator (left, right)) = generator (.left left right) := by
  exact extend_generator _ _

@[simp] theorem rightOneAxis_generator {X Y : SSet}
    (left : FactorSimplex X 1) (right : FactorSimplex Y 0) :
    rightOneAxis (generator (left, right)) = generator (.right left right) := by
  exact extend_generator _ _

theorem totalBoundaryOne_leftOneAxis {X Y : SSet}
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 1)) :
    totalBoundaryOne X Y (leftOneAxis current) =
      mapPairRight (factorBoundary Y 0) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, leftOneAxis_generator, totalBoundaryOne,
        extend_generator, totalBoundaryOneAtom, mapPairRight_generator,
        factorBoundary, factorBoundary_generator, factorBoundaryAtom]
      rw [Fin.sum_univ_two]
      norm_num
      module

theorem totalBoundaryOne_rightOneAxis {X Y : SSet}
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 0)) :
    totalBoundaryOne X Y (rightOneAxis current) =
      mapPairLeft (factorBoundary X 0) current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, rightOneAxis_generator, totalBoundaryOne,
        extend_generator, totalBoundaryOneAtom, mapPairLeft_generator,
        factorBoundary, factorBoundary_generator, factorBoundaryAtom]
      rw [Fin.sum_univ_two]
      norm_num
      module

theorem totalBoundaryTwo_leftAxis {X Y : SSet}
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 2)) :
    totalBoundaryTwo X Y (leftAxis current) =
      leftOneAxis (mapPairRight (factorBoundary Y 1) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, leftAxis_generator, totalBoundaryTwo,
        extend_generator, totalBoundaryTwoAtom, mapPairRight_generator,
        factorBoundary, factorBoundaryAtom]
      rw [Fin.sum_univ_three]
      norm_num
      module

theorem totalBoundaryTwo_middleAxis {X Y : SSet}
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    totalBoundaryTwo X Y (middleAxis current) =
      leftOneAxis (mapPairLeft (factorBoundary X 0) current) -
        rightOneAxis (mapPairRight (factorBoundary Y 0) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      have leftLaw :
          mapPairLeft (factorBoundary X 0) (generator (left, right)) =
            generator (face 0 left, right) - generator (face 1 left, right) := by
        rw [mapPairLeft_generator]
        have boundaryLaw :
            factorBoundary X 0 (generator left) =
              generator (face 0 left) - generator (face 1 left) := by
          simp [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
            sub_eq_add_neg]
        rw [boundaryLaw, pairCurrent_sub_left, pairCurrent_generator,
          pairCurrent_generator]
      have rightLaw :
          mapPairRight (factorBoundary Y 0) (generator (left, right)) =
            generator (left, face 0 right) - generator (left, face 1 right) := by
        rw [mapPairRight_generator]
        have boundaryLaw :
            factorBoundary Y 0 (generator right) =
              generator (face 0 right) - generator (face 1 right) := by
          simp [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
            sub_eq_add_neg]
        rw [boundaryLaw, pairCurrent_sub_right, pairCurrent_generator,
          pairCurrent_generator]
      have generatorLaw :
          totalBoundaryTwo X Y (middleAxis (generator (left, right))) =
            leftOneAxis
                (mapPairLeft (factorBoundary X 0) (generator (left, right))) -
              rightOneAxis
                (mapPairRight (factorBoundary Y 0) (generator (left, right))) := by
        simp only [middleAxis_generator, totalBoundaryTwo, extend_generator,
          totalBoundaryTwoAtom, leftLaw, rightLaw, map_sub,
          leftOneAxis_generator, rightOneAxis_generator]
        module
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simpa only [map_smul, smul_sub] using congrArg (coefficient • ·) generatorLaw

theorem totalBoundaryTwo_rightAxis {X Y : SSet}
    (current : Current (FactorSimplex X 2 × FactorSimplex Y 0)) :
    totalBoundaryTwo X Y (rightAxis current) =
      rightOneAxis (mapPairLeft (factorBoundary X 1) current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, rightAxis_generator, totalBoundaryTwo,
        extend_generator, totalBoundaryTwoAtom, mapPairLeft_generator,
        factorBoundary, factorBoundaryAtom]
      rw [Fin.sum_univ_three]
      norm_num
      module

theorem totalOneAxisReconstruction {X Y : SSet}
    (current : Current (TotalOneOccurrence X Y)) :
    leftOneAxis (leftOneAxisProjection current) +
      rightOneAxis (rightOneAxisProjection current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add]
      calc
        _ = (leftOneAxis (leftOneAxisProjection left) +
              rightOneAxis (rightOneAxisProjection left)) +
            (leftOneAxis (leftOneAxisProjection right) +
              rightOneAxis (rightOneAxisProjection right)) := by module
        _ = left + right := by rw [hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      cases occurrence with
      | left left right =>
          simp [leftOneAxisProjection, rightOneAxisProjection]
      | right left right =>
          simp [leftOneAxisProjection, rightOneAxisProjection]

theorem totalBoundaryOne_axisDecomposition {X Y : SSet}
    (current : Current (TotalOneOccurrence X Y)) :
    totalBoundaryOne X Y current =
      mapPairRight (factorBoundary Y 0) (leftOneAxisProjection current) +
        mapPairLeft (factorBoundary X 0) (rightOneAxisProjection current) := by
  nth_rewrite 1 [← totalOneAxisReconstruction current]
  rw [map_add, totalBoundaryOne_leftOneAxis, totalBoundaryOne_rightOneAxis]

def leftOuterBoundary {X Y : SSet} :
    Current (FactorSimplex X 0 × FactorSimplex Y 2) →ₗ[ℚ]
      Current (FactorSimplex X 0 × FactorSimplex Y 1) :=
  mapPairRight (factorBoundary Y 1)

def middleFirstBoundary {X Y : SSet} :
    Current (FactorSimplex X 1 × FactorSimplex Y 1) →ₗ[ℚ]
      Current (FactorSimplex X 0 × FactorSimplex Y 1) :=
  mapPairLeft (factorBoundary X 0)

def middleSecondBoundary {X Y : SSet} :
    Current (FactorSimplex X 1 × FactorSimplex Y 1) →ₗ[ℚ]
      Current (FactorSimplex X 1 × FactorSimplex Y 0) :=
  mapPairRight (factorBoundary Y 0)

def rightOuterBoundary {X Y : SSet} :
    Current (FactorSimplex X 2 × FactorSimplex Y 0) →ₗ[ℚ]
      Current (FactorSimplex X 1 × FactorSimplex Y 0) :=
  mapPairLeft (factorBoundary X 1)

@[simp] theorem leftAxisProjection_generator {X Y : SSet}
    (occurrence : TotalTwoOccurrence X Y) :
    leftAxisProjection (generator occurrence) = match occurrence with
      | .left left right => generator (left, right)
      | .middle _ _ => 0
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp] theorem middleAxisProjection_generator {X Y : SSet}
    (occurrence : TotalTwoOccurrence X Y) :
    middleAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .middle left right => generator (left, right)
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp] theorem rightAxisProjection_generator {X Y : SSet}
    (occurrence : TotalTwoOccurrence X Y) :
    rightAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .middle _ _ => 0
      | .right left right => generator (left, right) := by
  exact extend_generator _ _

@[simp] theorem leftOneAxisProjection_generator {X Y : SSet}
    (occurrence : TotalOneOccurrence X Y) :
    leftOneAxisProjection (generator occurrence) = match occurrence with
      | .left left right => generator (left, right)
      | .right _ _ => 0 := by
  exact extend_generator _ _

@[simp] theorem rightOneAxisProjection_generator {X Y : SSet}
    (occurrence : TotalOneOccurrence X Y) :
    rightOneAxisProjection (generator occurrence) = match occurrence with
      | .left _ _ => 0
      | .right left right => generator (left, right) := by
  exact extend_generator _ _

theorem totalTwoAxisReconstruction {X Y : SSet}
    (current : Current (TotalTwoOccurrence X Y)) :
    leftAxis (leftAxisProjection current) +
        middleAxis (middleAxisProjection current) +
      rightAxis (rightAxisProjection current) = current := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add current₁ current₂ h₁ h₂ =>
      simp only [map_add]
      calc
        _ = (leftAxis (leftAxisProjection current₁) +
                middleAxis (middleAxisProjection current₁) +
              rightAxis (rightAxisProjection current₁)) +
            (leftAxis (leftAxisProjection current₂) +
                middleAxis (middleAxisProjection current₂) +
              rightAxis (rightAxisProjection current₂)) := by module
        _ = current₁ + current₂ := by rw [h₁, h₂]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;> simp

theorem leftOneAxisProjection_totalBoundaryTwo {X Y : SSet}
    (current : Current (TotalTwoOccurrence X Y)) :
    leftOneAxisProjection (totalBoundaryTwo X Y current) =
      leftOuterBoundary (leftAxisProjection current) +
        middleFirstBoundary (middleAxisProjection current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;>
        simp [totalBoundaryTwo, totalBoundaryTwoAtom, leftOuterBoundary,
          middleFirstBoundary, factorBoundary, factorBoundaryAtom,
          Fin.sum_univ_two, Fin.sum_univ_three] <;>
        module

theorem rightOneAxisProjection_totalBoundaryTwo {X Y : SSet}
    (current : Current (TotalTwoOccurrence X Y)) :
    rightOneAxisProjection (totalBoundaryTwo X Y current) =
      -middleSecondBoundary (middleAxisProjection current) +
        rightOuterBoundary (rightAxisProjection current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul]
      cases occurrence <;>
        simp [totalBoundaryTwo, totalBoundaryTwoAtom, middleSecondBoundary,
          rightOuterBoundary, factorBoundary, factorBoundaryAtom,
          Fin.sum_univ_two, Fin.sum_univ_three] <;>
        module

theorem coupledAxisBoundaryEquations {X Y : SSet}
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    leftOuterBoundary (leftAxisProjection current) +
          middleFirstBoundary (middleAxisProjection current) = 0 ∧
      -middleSecondBoundary (middleAxisProjection current) +
          rightOuterBoundary (rightAxisProjection current) = 0 := by
  constructor
  · rw [← leftOneAxisProjection_totalBoundaryTwo, closed, map_zero]
  · rw [← rightOneAxisProjection_totalBoundaryTwo, closed, map_zero]

def pairFirstAugmentation {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X) :
    Current (FactorSimplex X 0 × Right) →ₗ[ℚ] Current Right :=
  extend fun pair => datum.augmentation (generator pair.1) • generator pair.2

def pairFirstBase {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X) :
    Current Right →ₗ[ℚ] Current (FactorSimplex X 0 × Right) :=
  extend fun right => generator (datum.basepoint, right)

@[simp] theorem pairFirstAugmentation_generator {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X) (left : FactorSimplex X 0) (right : Right) :
    pairFirstAugmentation datum (generator (left, right)) =
      datum.augmentation (generator left) • generator right := by
  exact extend_generator _ _

@[simp] theorem pairFirstBase_generator {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X) (right : Right) :
    pairFirstBase datum (generator right) = generator (datum.basepoint, right) := by
  exact extend_generator _ _

theorem pairFirstAugmentation_pairCurrent {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X)
    (left : FactorCurrent X 0) (right : Current Right) :
    pairFirstAugmentation datum (pairCurrent left right) =
      datum.augmentation left • right := by
  induction left using Finsupp.induction_linear generalizing right with
  | zero => simp [pairCurrent]
  | add left₁ left₂ h₁ h₂ =>
      simp only [pairCurrent_add_left, map_add, h₁, h₂]
      module
  | single leftOccurrence leftCoefficient =>
      induction right using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add right₁ right₂ h₁ h₂ =>
          simp only [pairCurrent_add_right, map_add, h₁, h₂, smul_add]
      | single rightOccurrence rightCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, pairFirstAugmentation_generator]
          module

theorem pairFirstBase_current {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X) (right : Current Right) :
    pairFirstBase datum right = pairCurrent (generator datum.basepoint) right := by
  induction right using Finsupp.induction_linear with
  | zero => simp [pairCurrent]
  | add left right hleft hright =>
      simp only [map_add, pairCurrent_add_right, hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul, pairFirstBase_generator,
        pairCurrent_smul_right, pairCurrent_generator]

/-! The degree-zero part of the product contraction.  It is already a complete diagonal
passage: two polarized factor paths are composed, then shuffled back into the shared source
simplex. -/

def productAugmentation {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    Current (DiagonalOccurrence X Y 0) →ₗ[ℚ] ℚ :=
  datumY.augmentation.comp (pairFirstAugmentation datumX)

def productH0SeparatedAtom {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (pair : DiagonalOccurrence X Y 0) : Current (TotalOneOccurrence X Y) :=
  leftOneAxis
      (pairCurrent (generator pair.1) (datumY.h0 (generator pair.2))) +
    rightOneAxis
      (pairCurrent (datumX.h0 (generator pair.1))
        (datumY.augmentation (generator pair.2) • generator datumY.basepoint))

def productH0Separated {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    Current (DiagonalOccurrence X Y 0) →ₗ[ℚ] Current (TotalOneOccurrence X Y) :=
  extend (productH0SeparatedAtom datumX datumY)

def productH0Diagonal {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    Current (DiagonalOccurrence X Y 0) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 1) :=
  (rejoinOne X Y).comp (productH0Separated datumX datumY)

@[simp] theorem productAugmentation_generator {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (left : FactorSimplex X 0) (right : FactorSimplex Y 0) :
    productAugmentation datumX datumY (generator (left, right)) =
      datumX.augmentation (generator left) *
        datumY.augmentation (generator right) := by
  simp [productAugmentation, LinearMap.comp_apply, smul_eq_mul]

theorem totalBoundaryOne_productH0SeparatedAtom {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (pair : DiagonalOccurrence X Y 0) :
    totalBoundaryOne X Y (productH0SeparatedAtom datumX datumY pair) =
      generator pair -
        productAugmentation datumX datumY (generator pair) •
          generator (datumX.basepoint, datumY.basepoint) := by
  rcases pair with ⟨left, right⟩
  simp only [productH0SeparatedAtom, map_add,
    totalBoundaryOne_leftOneAxis, totalBoundaryOne_rightOneAxis,
    mapPairRight_pairCurrent, mapPairLeft_pairCurrent,
    datumY.h0_boundary, datumX.h0_boundary,
    productAugmentation_generator]
  simp only [pairCurrent_sub_right, pairCurrent_sub_left,
    pairCurrent_generator, pairCurrent_smul_right, pairCurrent_smul_left]
  module

theorem totalBoundaryOne_productH0Separated {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 0)) :
    totalBoundaryOne X Y (productH0Separated datumX datumY current) =
      current - productAugmentation datumX datumY current •
        generator (datumX.basepoint, datumY.basepoint) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright, add_smul]
      module
  | single pair coefficient =>
      rw [show Finsupp.single pair coefficient =
          coefficient • generator pair by simp [generator]]
      simp only [map_smul, productH0Separated, extend_generator]
      simpa only [smul_sub, smul_smul, smul_eq_mul] using congrArg (coefficient • ·)
        (totalBoundaryOne_productH0SeparatedAtom datumX datumY pair)

/-- [proved-derived; formal-checked] The exact product vertex contraction after return to the
diagonal chart.  The only residue is the product augmentation at the addressed basepoint. -/
theorem diagonalBoundaryOne_productH0Diagonal {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 0)) :
    diagonalBoundaryOne X Y (productH0Diagonal datumX datumY current) =
      current - productAugmentation datumX datumY current •
        generator (datumX.basepoint, datumY.basepoint) := by
  have rejoinLaw := LinearMap.congr_fun (boundary_rejoinOne X Y)
      (productH0Separated datumX datumY current)
  change diagonalBoundaryOne X Y
      (rejoinOne X Y (productH0Separated datumX datumY current)) =
    totalBoundaryOne X Y (productH0Separated datumX datumY current) at rejoinLaw
  change diagonalBoundaryOne X Y
      (rejoinOne X Y (productH0Separated datumX datumY current)) = _
  rw [rejoinLaw, totalBoundaryOne_productH0Separated]

def pairSecondAugmentation {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y) :
    Current (Left × FactorSimplex Y 0) →ₗ[ℚ] Current Left :=
  extend fun pair => datum.augmentation (generator pair.2) • generator pair.1

def pairSecondBase {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y) :
    Current Left →ₗ[ℚ] Current (Left × FactorSimplex Y 0) :=
  extend fun left => generator (left, datum.basepoint)

@[simp] theorem pairSecondAugmentation_generator {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y) (left : Left) (right : FactorSimplex Y 0) :
    pairSecondAugmentation datum (generator (left, right)) =
      datum.augmentation (generator right) • generator left := by
  exact extend_generator _ _

@[simp] theorem pairSecondBase_generator {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y) (left : Left) :
    pairSecondBase datum (generator left) = generator (left, datum.basepoint) := by
  exact extend_generator _ _

theorem pairSecondAugmentation_pairCurrent {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y)
    (left : Current Left) (right : FactorCurrent Y 0) :
    pairSecondAugmentation datum (pairCurrent left right) =
      datum.augmentation right • left := by
  induction right using Finsupp.induction_linear generalizing left with
  | zero => simp [pairCurrent]
  | add right₁ right₂ h₁ h₂ =>
      simp only [pairCurrent_add_right, map_add, h₁, h₂]
      module
  | single rightOccurrence rightCoefficient =>
      induction left using Finsupp.induction_linear with
      | zero => simp [pairCurrent]
      | add left₁ left₂ h₁ h₂ =>
          simp only [pairCurrent_add_left, map_add, h₁, h₂, smul_add]
      | single leftOccurrence leftCoefficient =>
          rw [show Finsupp.single leftOccurrence leftCoefficient =
              leftCoefficient • generator leftOccurrence by simp [generator],
            show Finsupp.single rightOccurrence rightCoefficient =
              rightCoefficient • generator rightOccurrence by simp [generator]]
          simp only [pairCurrent_smul_left, pairCurrent_smul_right, map_smul,
            pairCurrent_generator, pairSecondAugmentation_generator]
          module

theorem pairSecondBase_current {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y) (left : Current Left) :
    pairSecondBase datum left = pairCurrent left (generator datum.basepoint) := by
  induction left using Finsupp.induction_linear with
  | zero => simp [pairCurrent]
  | add left right hleft hright =>
      simp only [map_add, pairCurrent_add_left, hleft, hright]
  | single occurrence coefficient =>
      rw [show Finsupp.single occurrence coefficient =
          coefficient • generator occurrence by simp [generator]]
      simp only [map_smul, pairSecondBase_generator,
        pairCurrent_smul_left, pairCurrent_generator]

theorem pairSecondAugmentation_mapPairLeft {Y : SSet} {Left Left' : Type*}
    (datum : LowDegreeCurrentDatum Y)
    (transport : Current Left →ₗ[ℚ] Current Left')
    (current : Current (Left × FactorSimplex Y 0)) :
    pairSecondAugmentation datum (mapPairLeft transport current) =
      transport (pairSecondAugmentation datum current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator,
        pairSecondAugmentation_pairCurrent,
        pairSecondAugmentation_generator]

theorem pairSecondAugmentation_mapPairRight_boundary {X Y : SSet}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 1)) :
    pairSecondAugmentation datum
        (mapPairRight (factorBoundary Y 0) current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairRight_generator,
        pairSecondAugmentation_pairCurrent,
        datum.augmentation_boundary_zero, zero_smul, smul_zero]

theorem mapPairRight_h0_boundary {Y : SSet} {Left : Type*}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (Left × FactorSimplex Y 0)) :
    mapPairRight (factorBoundary Y 0) (mapPairRight datum.h0 current) =
      current - pairSecondBase datum (pairSecondAugmentation datum current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      have generatorLaw :
          mapPairRight (factorBoundary Y 0)
              (mapPairRight datum.h0 (generator (left, right))) =
            generator (left, right) -
              pairSecondBase datum
                (pairSecondAugmentation datum (generator (left, right))) := by
        simp only [mapPairRight_generator, mapPairRight_pairCurrent,
          datum.h0_boundary, pairCurrent_sub_right, pairCurrent_generator,
          pairSecondAugmentation_generator, map_smul,
          pairSecondBase_generator, pairCurrent_smul_right]
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simpa only [map_smul, smul_sub] using congrArg (coefficient • ·) generatorLaw

theorem mapPairLeft_pairSecondBase {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y)
    (transport : FactorCurrent X 1 →ₗ[ℚ] FactorCurrent X 0)
    (current : FactorCurrent X 1) :
    mapPairLeft transport (pairSecondBase datumY current) =
      pairSecondBase datumY (transport current) := by
  rw [pairSecondBase_current, mapPairLeft_pairCurrent, pairSecondBase_current]

def productOneBaseResidual {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y) :
    Current (TotalOneOccurrence X Y) →ₗ[ℚ]
      Current (FactorSimplex X 1 × FactorSimplex Y 0) :=
  (pairSecondBase datumY).comp
    ((pairSecondAugmentation datumY).comp rightOneAxisProjection)

def productTotalOneFilling {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    Current (TotalOneOccurrence X Y) →ₗ[ℚ] Current (TotalTwoOccurrence X Y) :=
  leftAxis.comp ((mapPairRight (extendedH1 datumY)).comp leftOneAxisProjection) -
    middleAxis.comp ((mapPairRight datumY.h0).comp rightOneAxisProjection) +
    rightAxis.comp ((mapPairLeft (extendedH1 datumX)).comp
      (productOneBaseResidual datumY))

theorem productOneBaseResidual_closed {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalOneOccurrence X Y))
    (closed : totalBoundaryOne X Y current = 0) :
    mapPairLeft (factorBoundary X 0)
        (productOneBaseResidual datumY current) = 0 := by
  have equation := totalBoundaryOne_axisDecomposition current
  rw [closed] at equation
  have equation' :
      mapPairRight (factorBoundary Y 0) (leftOneAxisProjection current) +
        mapPairLeft (factorBoundary X 0) (rightOneAxisProjection current) = 0 :=
    equation.symm
  have rightBoundary :
      mapPairLeft (factorBoundary X 0) (rightOneAxisProjection current) =
        -mapPairRight (factorBoundary Y 0) (leftOneAxisProjection current) := by
    exact eq_neg_of_add_eq_zero_right equation'
  rw [productOneBaseResidual, LinearMap.comp_apply, LinearMap.comp_apply,
    mapPairLeft_pairSecondBase,
    ← pairSecondAugmentation_mapPairLeft, rightBoundary, map_neg,
    pairSecondAugmentation_mapPairRight_boundary, neg_zero, map_zero]

/-- [proved-derived; formal-checked] Every closed separated product one-current is the boundary
of one exact three-axis two-current.  The final outer term is the retained augmentation fibre
forced by coupling of the two polarized axes. -/
theorem totalBoundaryTwo_productTotalOneFilling {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalOneOccurrence X Y))
    (closed : totalBoundaryOne X Y current = 0) :
    totalBoundaryTwo X Y (productTotalOneFilling datumX datumY current) = current := by
  let leftCurrent := leftOneAxisProjection current
  let rightCurrent := rightOneAxisProjection current
  let baseResidual := productOneBaseResidual datumY current
  have equation := totalBoundaryOne_axisDecomposition current
  rw [closed] at equation
  have equation' :
      mapPairRight (factorBoundary Y 0) leftCurrent +
        mapPairLeft (factorBoundary X 0) rightCurrent = 0 := equation.symm
  have rightBoundary :
      mapPairLeft (factorBoundary X 0) rightCurrent =
        -mapPairRight (factorBoundary Y 0) leftCurrent := by
    exact eq_neg_of_add_eq_zero_right equation'
  have baseClosed : mapPairLeft (factorBoundary X 0) baseResidual = 0 := by
    exact productOneBaseResidual_closed datumY current closed
  simp only [productTotalOneFilling, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply]
  rw [map_add, map_sub,
    totalBoundaryTwo_leftAxis, totalBoundaryTwo_middleAxis,
    totalBoundaryTwo_rightAxis,
    mapPairRight_extendedH1_boundary,
    mapPairRight_h0_boundary,
    mapPairLeft_extendedH1_boundary,
    baseClosed, map_zero, sub_zero]
  have commute :
      mapPairLeft (factorBoundary X 0)
          (mapPairRight datumY.h0 rightCurrent) =
        mapPairRight datumY.h0
          (mapPairLeft (factorBoundary X 0) rightCurrent) :=
    mapPairLeft_right_commute (factorBoundary X 0) datumY.h0 rightCurrent
  rw [commute, rightBoundary, map_neg]
  dsimp only [leftCurrent, rightCurrent, baseResidual] at *
  simp only [productOneBaseResidual, LinearMap.comp_apply, map_sub, map_neg]
  calc
    _ = leftOneAxis (leftOneAxisProjection current) +
        rightOneAxis (rightOneAxisProjection current) := by module
    _ = current := totalOneAxisReconstruction current

def productH1Diagonal {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    Current (DiagonalOccurrence X Y 1) →ₗ[ℚ]
      Current (DiagonalOccurrence X Y 2) :=
  (rejoinTwo X Y).comp
      ((productTotalOneFilling datumX datumY) ∘ₗ (separateOne X Y)) -
    diagonalReconstructionFillerOne X Y

/-- [proved-derived; formal-checked] Product degree-one contraction on the genuine diagonal
current.  Separation, coupled filling, shuffle return, and reconstruction reflection compose to
the identity on every closed current. -/
theorem diagonalBoundaryTwo_productH1Diagonal_of_closed {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 1))
    (closed : diagonalBoundaryOne X Y current = 0) :
    diagonalBoundaryTwo X Y (productH1Diagonal datumX datumY current) = current := by
  have separateClosed :
      totalBoundaryOne X Y (separateOne X Y current) = 0 := by
    have law := LinearMap.congr_fun (boundary_separateOne X Y) current
    change totalBoundaryOne X Y (separateOne X Y current) =
      diagonalBoundaryOne X Y current at law
    rw [law, closed]
  have filled := totalBoundaryTwo_productTotalOneFilling datumX datumY
    (separateOne X Y current) separateClosed
  have rejoinLaw := LinearMap.congr_fun (boundary_rejoinTwo X Y)
    (productTotalOneFilling datumX datumY (separateOne X Y current))
  change diagonalBoundaryTwo X Y
      (rejoinTwo X Y
        (productTotalOneFilling datumX datumY (separateOne X Y current))) =
    rejoinOne X Y
      (totalBoundaryTwo X Y
        (productTotalOneFilling datumX datumY (separateOne X Y current))) at rejoinLaw
  have reconstructionLaw := LinearMap.congr_fun
    (boundary_diagonalReconstructionFillerOne X Y) current
  change diagonalBoundaryTwo X Y
      (diagonalReconstructionFillerOne X Y current) =
    diagonalRoundTripDefectOne X Y current at reconstructionLaw
  simp only [productH1Diagonal, LinearMap.sub_apply, LinearMap.comp_apply]
  rw [map_sub, rejoinLaw, filled,
    reconstructionLaw]
  simp [diagonalRoundTripDefectOne]

theorem pairFirstAugmentation_mapPairRight {X : SSet} {Right Right' : Type*}
    (datum : LowDegreeCurrentDatum X)
    (transport : Current Right →ₗ[ℚ] Current Right')
    (current : Current (FactorSimplex X 0 × Right)) :
    pairFirstAugmentation datum (mapPairRight transport current) =
      transport (pairFirstAugmentation datum current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairRight_generator,
        pairFirstAugmentation_pairCurrent,
        pairFirstAugmentation_generator]

theorem pairFirstAugmentation_mapPairLeft_boundary {X Y : SSet}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    pairFirstAugmentation datum
        (mapPairLeft (factorBoundary X 0) current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator,
        pairFirstAugmentation_pairCurrent,
        datum.augmentation_boundary_zero, zero_smul, smul_zero]

theorem mapPairLeft_h0_boundary {X : SSet} {Right : Type*}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 0 × Right)) :
    mapPairLeft (factorBoundary X 0) (mapPairLeft datum.h0 current) =
      current - pairFirstBase datum (pairFirstAugmentation datum current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
      module
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      have generatorLaw :
          mapPairLeft (factorBoundary X 0)
              (mapPairLeft datum.h0 (generator (left, right))) =
            generator (left, right) -
              pairFirstBase datum
                (pairFirstAugmentation datum (generator (left, right))) := by
        simp only [mapPairLeft_generator, mapPairLeft_pairCurrent,
          datum.h0_boundary, pairCurrent_sub_left, pairCurrent_generator,
          pairFirstAugmentation_generator, map_smul,
          pairFirstBase_generator, pairCurrent_smul_left]
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simpa only [map_smul, smul_sub] using congrArg (coefficient • ·) generatorLaw

theorem mapPairLeft_factorBoundary_sq {X Y : SSet}
    (datum : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 2 × FactorSimplex Y 0)) :
    mapPairLeft (factorBoundary X 0)
        (mapPairLeft (factorBoundary X 1) current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairLeft_generator, mapPairLeft_pairCurrent,
        datum.boundary_boundary_zero, pairCurrent_zero_left, smul_zero]

theorem mapPairRight_factorBoundary_sq {X Y : SSet}
    (datum : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 2)) :
    mapPairRight (factorBoundary Y 0)
        (mapPairRight (factorBoundary Y 1) current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, mapPairRight_generator, mapPairRight_pairCurrent,
        datum.boundary_boundary_zero, pairCurrent_zero_right, smul_zero]

def coupledRightMiddleContraction {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  rightMiddleAxis (mapPairLeft (extendedH1 datumX) current)

def coupledLeftMiddleCorrection {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  leftMiddleAxis
    (mapPairLeft datumX.h0
      (mapPairRight (extendedH1 datumY)
        (mapPairLeft (factorBoundary X 0) current)))

def coupledMiddleCorrection {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  coupledRightMiddleContraction datumX current -
    coupledLeftMiddleCorrection datumX datumY current

theorem coupledRightMiddleContraction_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    totalBoundaryThree X Y (coupledRightMiddleContraction datumX current) =
      middleAxis
          (current - mapPairLeft datumX.h0
            (mapPairLeft (factorBoundary X 0) current)) +
        rightAxis
          (mapPairLeft (extendedH1 datumX)
            (mapPairRight (factorBoundary Y 0) current)) := by
  rw [coupledRightMiddleContraction, totalBoundaryThree_rightMiddleAxis,
    mapPairLeft_extendedH1_boundary]
  rw [← mapPairLeft_right_commute]

theorem coupledLeftMiddleCorrection_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1))
    (firstBoundaryClosed :
      mapPairRight (factorBoundary Y 0)
          (mapPairLeft (factorBoundary X 0) current) = 0) :
    totalBoundaryThree X Y
        (coupledLeftMiddleCorrection datumX datumY current) =
      leftAxis
          (mapPairRight (extendedH1 datumY)
            (mapPairLeft (factorBoundary X 0) current)) -
        middleAxis
          (mapPairLeft datumX.h0
            (mapPairLeft (factorBoundary X 0) current)) := by
  let firstBoundary := mapPairLeft (factorBoundary X 0) current
  have firstAugmentation : pairFirstAugmentation datumX firstBoundary = 0 := by
    exact pairFirstAugmentation_mapPairLeft_boundary datumX current
  have liftedAugmentation :
      pairFirstAugmentation datumX
          (mapPairRight (extendedH1 datumY) firstBoundary) = 0 := by
    rw [pairFirstAugmentation_mapPairRight, firstAugmentation, map_zero]
  rw [coupledLeftMiddleCorrection, totalBoundaryThree_leftMiddleAxis]
  change leftAxis
      (mapPairLeft (factorBoundary X 0)
        (mapPairLeft datumX.h0
          (mapPairRight (extendedH1 datumY) firstBoundary))) -
    middleAxis
      (mapPairRight (factorBoundary Y 1)
        (mapPairLeft datumX.h0
          (mapPairRight (extendedH1 datumY) firstBoundary))) = _
  rw [mapPairLeft_h0_boundary, liftedAugmentation, map_zero, sub_zero]
  have commuteOuter :
      mapPairRight (factorBoundary Y 1)
          (mapPairLeft datumX.h0
            (mapPairRight (extendedH1 datumY) firstBoundary)) =
        mapPairLeft datumX.h0
          (mapPairRight (factorBoundary Y 1)
            (mapPairRight (extendedH1 datumY) firstBoundary)) := by
    exact (mapPairLeft_right_commute datumX.h0 (factorBoundary Y 1)
      (mapPairRight (extendedH1 datumY) firstBoundary)).symm
  rw [commuteOuter, mapPairRight_extendedH1_boundary,
    firstBoundaryClosed]
  simp [firstBoundary]

theorem coupledMiddleCorrection_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1))
    (firstBoundaryClosed :
      mapPairRight (factorBoundary Y 0)
          (mapPairLeft (factorBoundary X 0) current) = 0) :
    totalBoundaryThree X Y (coupledMiddleCorrection datumX datumY current) =
      middleAxis current +
          rightAxis
            (mapPairLeft (extendedH1 datumX)
              (mapPairRight (factorBoundary Y 0) current)) -
        leftAxis
          (mapPairRight (extendedH1 datumY)
            (mapPairLeft (factorBoundary X 0) current)) := by
  rw [coupledMiddleCorrection, map_sub,
    coupledRightMiddleContraction_boundary,
    coupledLeftMiddleCorrection_boundary datumX datumY current firstBoundaryClosed]
  simp only [map_sub]
  module

theorem mixedFirstBoundary_closed_of_totalBoundary {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    mapPairRight (factorBoundary Y 0)
        (mapPairLeft (factorBoundary X 0)
          (middleAxisProjection current)) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).1
  change mapPairRight (factorBoundary Y 1) (leftAxisProjection current) +
    mapPairLeft (factorBoundary X 0) (middleAxisProjection current) = 0 at equation
  have returnedBoundary :
      mapPairLeft (factorBoundary X 0) (middleAxisProjection current) =
        -mapPairRight (factorBoundary Y 1) (leftAxisProjection current) := by
    exact eq_neg_of_add_eq_zero_right equation
  rw [returnedBoundary, map_neg,
    mapPairRight_factorBoundary_sq datumY, neg_zero]

theorem mixedSecondBoundary_closed_of_totalBoundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    mapPairLeft (factorBoundary X 0)
        (mapPairRight (factorBoundary Y 0)
          (middleAxisProjection current)) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).2
  change -mapPairRight (factorBoundary Y 0) (middleAxisProjection current) +
    mapPairLeft (factorBoundary X 1) (rightAxisProjection current) = 0 at equation
  have returnedBoundary :
      mapPairRight (factorBoundary Y 0) (middleAxisProjection current) =
        mapPairLeft (factorBoundary X 1) (rightAxisProjection current) := by
    have reversed := eq_neg_of_add_eq_zero_right equation
    simpa using reversed.symm
  rw [returnedBoundary, mapPairLeft_factorBoundary_sq datumX]

def correctedFirstOuter {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) :
    Current (FactorSimplex X 0 × FactorSimplex Y 2) :=
  leftAxisProjection current +
    mapPairRight (extendedH1 datumY)
      (mapPairLeft (factorBoundary X 0) (middleAxisProjection current))

def correctedSecondOuter {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X)
    (current : Current (TotalTwoOccurrence X Y)) :
    Current (FactorSimplex X 2 × FactorSimplex Y 0) :=
  rightAxisProjection current -
    mapPairLeft (extendedH1 datumX)
      (mapPairRight (factorBoundary Y 0) (middleAxisProjection current))

theorem correctedFirstOuter_closed {X Y : SSet}
    (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    mapPairRight (factorBoundary Y 1) (correctedFirstOuter datumY current) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).1
  have returnedClosed := mixedFirstBoundary_closed_of_totalBoundary datumY current closed
  rw [correctedFirstOuter, map_add, mapPairRight_extendedH1_boundary,
    returnedClosed]
  simpa [leftOuterBoundary, middleFirstBoundary] using equation

theorem correctedSecondOuter_closed {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    mapPairLeft (factorBoundary X 1) (correctedSecondOuter datumX current) = 0 := by
  have equation := (coupledAxisBoundaryEquations current closed).2
  have returnedClosed := mixedSecondBoundary_closed_of_totalBoundary datumX current closed
  rw [correctedSecondOuter, map_sub, mapPairLeft_extendedH1_boundary,
    returnedClosed]
  change -mapPairRight (factorBoundary Y 0) (middleAxisProjection current) +
    mapPairLeft (factorBoundary X 1) (rightAxisProjection current) = 0 at equation
  simpa [sub_eq_add_neg, add_comm] using equation

/-- [proved-derived; formal-checked] Exact coupled product compression.  A closed current is
homologous to two separately closed outer currents, and the complete mixed-axis reconstruction
fibre is the displayed polarized degree-three current. -/
theorem coupledMiddleCorrection_reduces_to_outer {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    current - totalBoundaryThree X Y
        (coupledMiddleCorrection datumX datumY (middleAxisProjection current)) =
      leftAxis (correctedFirstOuter datumY current) +
        rightAxis (correctedSecondOuter datumX current) := by
  have returnedClosed := mixedFirstBoundary_closed_of_totalBoundary datumY current closed
  rw [coupledMiddleCorrection_boundary _ _ _ returnedClosed]
  nth_rewrite 1 [← totalTwoAxisReconstruction current]
  simp only [correctedFirstOuter, correctedSecondOuter, map_add, map_sub]
  module

/-! ## Complete outer normalization

The middle correction leaves one closed degree-two current in each factor, still paired with an
arbitrary degree-zero current in the other factor.  Applying the retained degree-zero contraction
normalizes those arbitrary vertices to the two declared basepoints.  This is the exact final seam
before a product `H₂` class splits into its two factor classes. -/

/-- The closed degree-two current returned in the first factor after augmenting the second
degree-zero coordinate. -/
def productFirstFactorDegreeTwoCurrent {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) : FactorCurrent X 2 :=
  pairSecondAugmentation datumY (correctedSecondOuter datumX current)

/-- The closed degree-two current returned in the second factor after augmenting the first
degree-zero coordinate. -/
def productSecondFactorDegreeTwoCurrent {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) : FactorCurrent Y 2 :=
  pairFirstAugmentation datumX (correctedFirstOuter datumY current)

/-- [proved-derived; formal-checked] The first returned factor current is closed whenever the
complete product current is closed. -/
theorem productFirstFactorDegreeTwoCurrent_closed {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    factorBoundary X 1
        (productFirstFactorDegreeTwoCurrent datumX datumY current) = 0 := by
  rw [productFirstFactorDegreeTwoCurrent,
    ← pairSecondAugmentation_mapPairLeft]
  rw [correctedSecondOuter_closed datumX current closed, map_zero]

/-- [proved-derived; formal-checked] The second returned factor current is closed under the same
complete closure hypothesis. -/
theorem productSecondFactorDegreeTwoCurrent_closed {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    factorBoundary Y 1
        (productSecondFactorDegreeTwoCurrent datumX datumY current) = 0 := by
  rw [productSecondFactorDegreeTwoCurrent,
    ← pairFirstAugmentation_mapPairRight]
  rw [correctedFirstOuter_closed datumY current closed, map_zero]

/-- Normalize the arbitrary first-factor vertices of the left outer current. -/
def leftOuterNormalizationCorrection {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) :
    Current (TotalThreeOccurrence X Y) :=
  leftMiddleAxis (mapPairLeft datumX.h0 (correctedFirstOuter datumY current))

/-- Normalize the arbitrary second-factor vertices of the right outer current. -/
def rightOuterNormalizationCorrection {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) :
    Current (TotalThreeOccurrence X Y) :=
  rightMiddleAxis (mapPairRight datumY.h0 (correctedSecondOuter datumX current))

theorem leftOuterNormalizationCorrection_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    totalBoundaryThree X Y
        (leftOuterNormalizationCorrection datumX datumY current) =
      leftAxis
        (correctedFirstOuter datumY current -
          pairFirstBase datumX
            (productSecondFactorDegreeTwoCurrent datumX datumY current)) := by
  rw [leftOuterNormalizationCorrection, totalBoundaryThree_leftMiddleAxis,
    mapPairLeft_h0_boundary]
  have commute :
      mapPairRight (factorBoundary Y 1)
          (mapPairLeft datumX.h0 (correctedFirstOuter datumY current)) =
        mapPairLeft datumX.h0
          (mapPairRight (factorBoundary Y 1)
            (correctedFirstOuter datumY current)) :=
    (mapPairLeft_right_commute datumX.h0 (factorBoundary Y 1)
      (correctedFirstOuter datumY current)).symm
  rw [commute, correctedFirstOuter_closed datumY current closed, map_zero]
  simp [productSecondFactorDegreeTwoCurrent]

theorem rightOuterNormalizationCorrection_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    totalBoundaryThree X Y
        (rightOuterNormalizationCorrection datumX datumY current) =
      rightAxis
        (correctedSecondOuter datumX current -
          pairSecondBase datumY
            (productFirstFactorDegreeTwoCurrent datumX datumY current)) := by
  rw [rightOuterNormalizationCorrection, totalBoundaryThree_rightMiddleAxis]
  have commute :
      mapPairLeft (factorBoundary X 1)
          (mapPairRight datumY.h0 (correctedSecondOuter datumX current)) =
        mapPairRight datumY.h0
          (mapPairLeft (factorBoundary X 1)
            (correctedSecondOuter datumX current)) :=
    mapPairLeft_right_commute (factorBoundary X 1) datumY.h0
      (correctedSecondOuter datumX current)
  rw [commute, correctedSecondOuter_closed datumX current closed, map_zero,
    mapPairRight_h0_boundary]
  simp [productFirstFactorDegreeTwoCurrent]

/-- The complete source-level degree-three witness: mixed-axis filling followed by both exact
outer normalizations. -/
def productDegreeTwoNormalizationFiller {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) :
    Current (TotalThreeOccurrence X Y) :=
  coupledMiddleCorrection datumX datumY (middleAxisProjection current) +
    leftOuterNormalizationCorrection datumX datumY current +
    rightOuterNormalizationCorrection datumX datumY current

/-- [proved-derived; formal-checked] Every closed separated product degree-two current is the two
closed factor currents at the retained basepoints plus the boundary of one explicit degree-three
current.  No Künneth rank count or quotient-only argument enters this decomposition. -/
theorem productDegreeTwoNormalizationFiller_boundary {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y))
    (closed : totalBoundaryTwo X Y current = 0) :
    totalBoundaryThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY current) =
      current -
        (leftAxis
            (pairFirstBase datumX
              (productSecondFactorDegreeTwoCurrent datumX datumY current)) +
          rightAxis
            (pairSecondBase datumY
              (productFirstFactorDegreeTwoCurrent datumX datumY current))) := by
  have middleReduction :=
    coupledMiddleCorrection_reduces_to_outer datumX datumY current closed
  have middleBoundary :
      totalBoundaryThree X Y
          (coupledMiddleCorrection datumX datumY (middleAxisProjection current)) =
        current -
          (leftAxis (correctedFirstOuter datumY current) +
            rightAxis (correctedSecondOuter datumX current)) := by
    calc
      totalBoundaryThree X Y
          (coupledMiddleCorrection datumX datumY (middleAxisProjection current)) =
          current -
            (current - totalBoundaryThree X Y
              (coupledMiddleCorrection datumX datumY
                (middleAxisProjection current))) := by module
      _ = current -
          (leftAxis (correctedFirstOuter datumY current) +
            rightAxis (correctedSecondOuter datumX current)) := by
        rw [middleReduction]
  rw [productDegreeTwoNormalizationFiller, map_add, map_add,
    leftOuterNormalizationCorrection_boundary datumX datumY current closed,
    rightOuterNormalizationCorrection_boundary datumX datumY current closed]
  rw [middleBoundary]
  simp only [map_sub]
  module

/-! ## Product boundary nilpotence

The factor data already carries the two degree-two boundary squares.  The product square is not
another hypothesis: the two outer terms vanish by those factor laws and the two middle terms
cancel by exact interchange of the independent incidences. -/

/-- [proved-derived; formal-checked] The separated product boundary squares to zero. -/
theorem totalBoundaryOne_totalBoundaryTwo {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (TotalTwoOccurrence X Y)) :
    totalBoundaryOne X Y (totalBoundaryTwo X Y current) = 0 := by
  nth_rewrite 1 [← totalTwoAxisReconstruction current]
  simp only [map_add, map_sub, totalBoundaryTwo_leftAxis, totalBoundaryTwo_middleAxis,
    totalBoundaryTwo_rightAxis, totalBoundaryOne_leftOneAxis,
    totalBoundaryOne_rightOneAxis]
  have commute :
      mapPairRight (factorBoundary Y 0)
          (mapPairLeft (factorBoundary X 0) (middleAxisProjection current)) =
        mapPairLeft (factorBoundary X 0)
          (mapPairRight (factorBoundary Y 0) (middleAxisProjection current)) :=
    (mapPairLeft_right_commute (factorBoundary X 0) (factorBoundary Y 0)
      (middleAxisProjection current)).symm
  rw [mapPairRight_factorBoundary_sq datumY,
    mapPairLeft_factorBoundary_sq datumX, commute]
  module

/-- [proved-derived; formal-checked] The shared-source diagonal product boundary also squares to
zero.  Separation is used only as an exact chart: no occurrence or mixed-axis seam is discarded. -/
theorem diagonalBoundaryOne_diagonalBoundaryTwo {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 2)) :
    diagonalBoundaryOne X Y (diagonalBoundaryTwo X Y current) = 0 := by
  have separateOneLaw := LinearMap.congr_fun (boundary_separateOne X Y)
    (diagonalBoundaryTwo X Y current)
  have separateTwoLaw := LinearMap.congr_fun (boundary_separateTwo X Y) current
  have separateOneLaw' :
      totalBoundaryOne X Y
          (separateOne X Y (diagonalBoundaryTwo X Y current)) =
        diagonalBoundaryOne X Y (diagonalBoundaryTwo X Y current) := by
    simpa only [LinearMap.comp_apply] using separateOneLaw
  have separateTwoLaw' :
      totalBoundaryTwo X Y (separateTwo X Y current) =
        separateOne X Y (diagonalBoundaryTwo X Y current) := by
    simpa only [LinearMap.comp_apply] using separateTwoLaw
  calc
    diagonalBoundaryOne X Y (diagonalBoundaryTwo X Y current) =
        totalBoundaryOne X Y
          (separateOne X Y (diagonalBoundaryTwo X Y current)) := separateOneLaw'.symm
    _ = totalBoundaryOne X Y
          (totalBoundaryTwo X Y (separateTwo X Y current)) := by rw [separateTwoLaw']
    _ = 0 := totalBoundaryOne_totalBoundaryTwo datumX datumY _

/-! ## The exact polarized middle correction -/

def middlePolarizedFilling {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (left : FactorSimplex X 1) (right : FactorSimplex Y 1) :
  Current (TotalThreeOccurrence X Y) :=
  rightMiddleAxis
      (pairCurrent (datumX.h1 (h1ClosedPart datumX (generator left)))
        (generator right))

theorem boundary_middlePolarizedFilling {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (left : FactorSimplex X 1) (right : FactorSimplex Y 1)
    (hleft : factorBoundary X 0 (generator left) = 0)
    (hright : factorBoundary Y 0 (generator right) = 0) :
    totalBoundaryThree X Y (middlePolarizedFilling datumX datumY left right) =
      middleAxis (pairCurrent (generator left) (generator right)) := by
  rw [middlePolarizedFilling, totalBoundaryThree_rightMiddle]
  have hx := h1_extended_boundary datumX (generator left)
  rw [hleft] at hx
  rw [hright]
  simp only [pairCurrent_zero_right]
  rw [hx]
  simp only [pairCurrent_add_left, pairCurrent_neg_left, pairCurrent_generator,
    map_sub]
  simp

/-! A sum of polarized middle terms gives the corresponding actual degree-three current. -/

def middlePolarizedFillingCurrent {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    Current (TotalThreeOccurrence X Y) :=
  extend (fun pair => middlePolarizedFilling datumX datumY pair.1 pair.2) current

theorem boundary_middlePolarizedFillingCurrent {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1))
    (closedLeft : ∀ pair : FactorSimplex X 1 × FactorSimplex Y 1,
      factorBoundary X 0 (generator pair.1) = 0)
    (closedRight : ∀ pair : FactorSimplex X 1 × FactorSimplex Y 1,
      factorBoundary Y 0 (generator pair.2) = 0) :
    totalBoundaryThree X Y (middlePolarizedFillingCurrent datumX datumY current) =
      middleAxis current := by
  induction current using Finsupp.induction_linear with
  | zero => simp [middlePolarizedFillingCurrent]
  | add current₁ current₂ h₁ h₂ =>
      simp only [middlePolarizedFillingCurrent, map_add]
      change totalBoundaryThree X Y
          (middlePolarizedFillingCurrent datumX datumY current₁) +
          totalBoundaryThree X Y
            (middlePolarizedFillingCurrent datumX datumY current₂) =
        middleAxis current₁ + middleAxis current₂
      rw [h₁, h₂]
  | single pair coefficient =>
      rw [show Finsupp.single pair coefficient = coefficient • generator pair by simp [generator]]
      simp only [middlePolarizedFillingCurrent, map_smul, extend_generator]
      rw [boundary_middlePolarizedFilling datumX datumY pair.1 pair.2
        (closedLeft pair) (closedRight pair)]
      simp only [pairCurrent_generator]

/-! ## A genuine product simplicial set as the diagonal pair chart

The algebra above was intentionally independent of any chosen product presentation.  The next
object is the exact adapter it requires: every genuine product simplex is identified with its two
coordinate simplices, and the identification commutes with every face.  This is sufficient to
transport all low-degree contraction data; no point count or homology quotient enters. -/

/-- [definition] A source simplicial set whose complete simplices are the diagonal pairs of two
factor simplicial sets, with face transport retained as part of the datum. -/
structure ProductSimplexRealization (Product X Y : SSet) where
  simplexEquiv : ∀ degree : ℕ,
    FactorSimplex Product degree ≃ DiagonalOccurrence X Y degree
  face_naturality : ∀ {degree : ℕ} (omitted : Fin (degree + 2))
      (simplex : FactorSimplex Product (degree + 1)),
    simplexEquiv degree (face omitted simplex) =
      diagonalFace omitted (simplexEquiv (degree + 1) simplex)

/-- The complete finite current transported through a product-simplex realization. -/
def realizedProductCurrentEquiv {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y) (degree : ℕ) :
    FactorCurrent Product degree ≃ₗ[ℚ]
      Current (DiagonalOccurrence X Y degree) :=
  Finsupp.domLCongr (realization.simplexEquiv degree)

@[simp]
theorem realizedProductCurrentEquiv_generator {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y) {degree : ℕ}
    (simplex : FactorSimplex Product degree) :
    realizedProductCurrentEquiv realization degree (generator simplex) =
      generator (realization.simplexEquiv degree simplex) := by
  simp [realizedProductCurrentEquiv, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, generator]

/-- [proved-derived; formal-checked] The genuine degree-one boundary is the diagonal pair
boundary under every product realization. -/
theorem realizedProductCurrentEquiv_boundary_one {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 1) :
    realizedProductCurrentEquiv realization 0
        (factorBoundary Product 0 current) =
      diagonalBoundaryOne X Y
        (realizedProductCurrentEquiv realization 1 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryOne, extend_generator, diagonalBoundaryOneAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_two]
      norm_num
      module

/-- [proved-derived; formal-checked] The genuine degree-two boundary is the complete diagonal
pair boundary, including all three faces. -/
theorem realizedProductCurrentEquiv_boundary_two {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 2) :
    realizedProductCurrentEquiv realization 1
        (factorBoundary Product 1 current) =
      diagonalBoundaryTwo X Y
        (realizedProductCurrentEquiv realization 2 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryTwo, extend_generator, diagonalBoundaryTwoAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_three]
      norm_num
      module

/-- [proved-derived; formal-checked] The genuine degree-three boundary is the complete four-face
diagonal pair boundary. -/
theorem realizedProductCurrentEquiv_boundary_three {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 3) :
    realizedProductCurrentEquiv realization 2
        (factorBoundary Product 2 current) =
      diagonalBoundaryThree X Y
        (realizedProductCurrentEquiv realization 3 current) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, factorBoundary_generator,
        factorBoundaryAtom, map_sum, realizedProductCurrentEquiv_generator,
        diagonalBoundaryThree, extend_generator, diagonalBoundaryThreeAtom]
      simp_rw [realization.face_naturality]
      rw [Fin.sum_univ_four]
      norm_num
      module

/-- The first factor current extracted from one genuine product degree-two current. -/
def realizedProductFirstFactorDegreeTwoCurrent {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent X 2 :=
  productFirstFactorDegreeTwoCurrent datumX datumY
    (separateTwo X Y (realizedProductCurrentEquiv realization 2 current))

/-- The second factor current extracted from the same complete occurrence population. -/
def realizedProductSecondFactorDegreeTwoCurrent {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent Y 2 :=
  productSecondFactorDegreeTwoCurrent datumX datumY
    (separateTwo X Y (realizedProductCurrentEquiv realization 2 current))

theorem realizedProductSeparatedDegreeTwo_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    totalBoundaryTwo X Y
        (separateTwo X Y (realizedProductCurrentEquiv realization 2 current)) = 0 := by
  have diagonalClosed :
      diagonalBoundaryTwo X Y
          (realizedProductCurrentEquiv realization 2 current) = 0 := by
    rw [← realizedProductCurrentEquiv_boundary_two, closed, map_zero]
  have law := LinearMap.congr_fun (boundary_separateTwo X Y)
    (realizedProductCurrentEquiv realization 2 current)
  simpa only [LinearMap.comp_apply, diagonalClosed, map_zero] using law

theorem realizedProductFirstFactorDegreeTwoCurrent_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary X 1
        (realizedProductFirstFactorDegreeTwoCurrent
          realization datumX datumY current) = 0 := by
  exact productFirstFactorDegreeTwoCurrent_closed datumX datumY _
    (realizedProductSeparatedDegreeTwo_closed realization current closed)

theorem realizedProductSecondFactorDegreeTwoCurrent_closed {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary Y 1
        (realizedProductSecondFactorDegreeTwoCurrent
          realization datumX datumY current) = 0 := by
  exact productSecondFactorDegreeTwoCurrent_closed datumX datumY _
    (realizedProductSeparatedDegreeTwo_closed realization current closed)

/-- The complete degree-three reconstruction witness returned in the genuine source chart. -/
def realizedProductDegreeTwoNormalizationFiller {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2) : FactorCurrent Product 3 :=
  (realizedProductCurrentEquiv realization 3).symm
    (rejoinThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY
          (separateTwo X Y
            (realizedProductCurrentEquiv realization 2 current))) -
      diagonalReconstructionFillerTwo X Y
        (realizedProductCurrentEquiv realization 2 current))

/-- [proved-derived; formal-checked] The complete product decomposition in the genuine simplex
chart.  The returned factor cycles are closed, and the displayed degree-three current witnesses
the difference between the source cycle and their two basepoint inclusions. -/
theorem realizedProductDegreeTwoNormalizationFiller_boundary {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : FactorCurrent Product 2)
    (closed : factorBoundary Product 1 current = 0) :
    factorBoundary Product 2
        (realizedProductDegreeTwoNormalizationFiller
          realization datumX datumY current) =
      current -
        (realizedProductCurrentEquiv realization 2).symm
          (rejoinTwo X Y
            (leftAxis
                (pairFirstBase datumX
                  (realizedProductSecondFactorDegreeTwoCurrent
                    realization datumX datumY current)) +
              rightAxis
                (pairSecondBase datumY
                  (realizedProductFirstFactorDegreeTwoCurrent
                    realization datumX datumY current)))) := by
  let diagonal := realizedProductCurrentEquiv realization 2 current
  let separated := separateTwo X Y diagonal
  have diagonalClosed : diagonalBoundaryTwo X Y diagonal = 0 := by
    dsimp [diagonal]
    rw [← realizedProductCurrentEquiv_boundary_two, closed, map_zero]
  have separatedClosed : totalBoundaryTwo X Y separated = 0 := by
    have law := LinearMap.congr_fun (boundary_separateTwo X Y) diagonal
    simpa only [LinearMap.comp_apply, diagonalClosed, map_zero] using law
  apply (realizedProductCurrentEquiv realization 2).injective
  rw [realizedProductCurrentEquiv_boundary_three]
  simp only [realizedProductDegreeTwoNormalizationFiller,
    LinearEquiv.apply_symm_apply, map_sub]
  change diagonalBoundaryThree X Y
        (rejoinThree X Y
          (productDegreeTwoNormalizationFiller datumX datumY separated)) -
      diagonalBoundaryThree X Y
        (diagonalReconstructionFillerTwo X Y diagonal) = _
  have rejoinBoundary := LinearMap.congr_fun (boundary_rejoinThree X Y)
    (productDegreeTwoNormalizationFiller datumX datumY separated)
  change diagonalBoundaryThree X Y
      (rejoinThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY separated)) =
    rejoinTwo X Y
      (totalBoundaryThree X Y
        (productDegreeTwoNormalizationFiller datumX datumY separated)) at rejoinBoundary
  rw [rejoinBoundary,
    productDegreeTwoNormalizationFiller_boundary datumX datumY separated separatedClosed]
  have defectBoundary :=
    diagonalRoundTripDefectTwo_eq_boundary_of_cycle diagonal diagonalClosed
  change rejoinTwo X Y (separateTwo X Y diagonal) - diagonal =
    diagonalBoundaryThree X Y
      (diagonalReconstructionFillerTwo X Y diagonal) at defectBoundary
  rw [← defectBoundary]
  simp only [map_sub, map_add,
    realizedProductFirstFactorDegreeTwoCurrent,
    realizedProductSecondFactorDegreeTwoCurrent, diagonal, separated,
    LinearEquiv.apply_symm_apply]
  module

/-- [proved-derived; formal-checked] The product augmentation kills every diagonal one-boundary.
This is the exact statement that an oriented edge does not create or destroy its total degree-zero
population. -/
theorem productAugmentation_diagonalBoundaryOne {X Y : SSet}
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y)
    (current : Current (DiagonalOccurrence X Y 1)) :
    productAugmentation datumX datumY
        (diagonalBoundaryOne X Y current) = 0 := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [hleft, hright]
  | single pair coefficient =>
      rcases pair with ⟨left, right⟩
      have leftEquality :
          datumX.augmentation (generator (face 0 left)) =
            datumX.augmentation (generator (face 1 left)) := by
        apply sub_eq_zero.mp
        simpa [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
          sub_eq_add_neg] using
          datumX.augmentation_boundary_zero (generator left)
      have rightEquality :
          datumY.augmentation (generator (face 0 right)) =
            datumY.augmentation (generator (face 1 right)) := by
        apply sub_eq_zero.mp
        simpa [factorBoundary, factorBoundaryAtom, Fin.sum_univ_two,
          sub_eq_add_neg] using
          datumY.augmentation_boundary_zero (generator right)
      rw [show Finsupp.single (left, right) coefficient =
          coefficient • generator (left, right) by simp [generator]]
      simp only [map_smul, diagonalBoundaryOne, extend_generator,
        diagonalBoundaryOneAtom, map_sub, smul_sub]
      simp only [diagonalFace]
      rw [productAugmentation_generator, productAugmentation_generator]
      rw [leftEquality, rightEquality]
      module

/-- The retained basepoint in a genuine product chart. -/
def realizedProductBasepoint {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorSimplex Product 0 :=
  (realization.simplexEquiv 0).symm (datumX.basepoint, datumY.basepoint)

@[simp]
theorem realizedProductCurrentEquiv_basepoint {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    realizedProductCurrentEquiv realization 0
        (generator (realizedProductBasepoint realization datumX datumY)) =
      generator (datumX.basepoint, datumY.basepoint) := by
  rw [realizedProductCurrentEquiv_generator]
  simp [realizedProductBasepoint]

/-- Product augmentation transported to the genuine source simplicial set. -/
def realizedProductAugmentation {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 0 →ₗ[ℚ] ℚ :=
  (productAugmentation datumX datumY).comp
    (realizedProductCurrentEquiv realization 0).toLinearMap

/-- Product degree-zero contraction transported back to the genuine source chart. -/
def realizedProductH0 {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 0 →ₗ[ℚ] FactorCurrent Product 1 :=
  (realizedProductCurrentEquiv realization 1).symm.toLinearMap.comp
    ((productH0Diagonal datumX datumY).comp
      (realizedProductCurrentEquiv realization 0).toLinearMap)

/-- Product degree-one contraction transported back to the genuine source chart. -/
def realizedProductH1 {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    FactorCurrent Product 1 →ₗ[ℚ] FactorCurrent Product 2 :=
  (realizedProductCurrentEquiv realization 2).symm.toLinearMap.comp
    ((productH1Diagonal datumX datumY).comp
      (realizedProductCurrentEquiv realization 1).toLinearMap)

/-- [proved-derived; formal-checked] Low-degree contraction data composes across a genuine
product realization.  The construction retains the coordinate-simplex equivalence, the complete
mixed-axis current, and both inverse current charts. -/
def realizedProductLowDegreeCurrentDatum {Product X Y : SSet}
    (realization : ProductSimplexRealization Product X Y)
    (datumX : LowDegreeCurrentDatum X) (datumY : LowDegreeCurrentDatum Y) :
    LowDegreeCurrentDatum Product where
  basepoint := realizedProductBasepoint realization datumX datumY
  augmentation := realizedProductAugmentation realization datumX datumY
  augmentation_basepoint := by
    change productAugmentation datumX datumY
        (realizedProductCurrentEquiv realization 0
          (generator (realizedProductBasepoint realization datumX datumY))) = 1
    rw [realizedProductCurrentEquiv_basepoint,
      productAugmentation_generator, datumX.augmentation_basepoint,
      datumY.augmentation_basepoint, one_mul]
  augmentation_boundary_zero := by
    intro current
    change productAugmentation datumX datumY
        (realizedProductCurrentEquiv realization 0
          (factorBoundary Product 0 current)) = 0
    rw [realizedProductCurrentEquiv_boundary_one,
      productAugmentation_diagonalBoundaryOne]
  boundary_boundary_zero := by
    intro current
    apply (realizedProductCurrentEquiv realization 0).injective
    rw [map_zero, realizedProductCurrentEquiv_boundary_one,
      realizedProductCurrentEquiv_boundary_two,
      diagonalBoundaryOne_diagonalBoundaryTwo datumX datumY]
  h0 := realizedProductH0 realization datumX datumY
  h0_boundary := by
    intro current
    apply (realizedProductCurrentEquiv realization 0).injective
    calc
      realizedProductCurrentEquiv realization 0
          (factorBoundary Product 0
            (realizedProductH0 realization datumX datumY current)) =
        diagonalBoundaryOne X Y
          (realizedProductCurrentEquiv realization 1
            (realizedProductH0 realization datumX datumY current)) :=
        realizedProductCurrentEquiv_boundary_one realization _
      _ = diagonalBoundaryOne X Y
          (productH0Diagonal datumX datumY
            (realizedProductCurrentEquiv realization 0 current)) := by
        apply congrArg (diagonalBoundaryOne X Y)
        simp only [realizedProductH0, LinearMap.comp_apply]
        exact (realizedProductCurrentEquiv realization 1).apply_symm_apply _
      _ = realizedProductCurrentEquiv realization 0 current -
          productAugmentation datumX datumY
              (realizedProductCurrentEquiv realization 0 current) •
            generator (datumX.basepoint, datumY.basepoint) :=
        diagonalBoundaryOne_productH0Diagonal datumX datumY _
      _ = realizedProductCurrentEquiv realization 0
          (current -
            realizedProductAugmentation realization datumX datumY current •
              generator
                (realizedProductBasepoint realization datumX datumY)) := by
        rw [map_sub, map_smul, realizedProductCurrentEquiv_basepoint]
        rfl
  h1 := realizedProductH1 realization datumX datumY
  h1_boundary_of_closed := by
    intro current closed
    apply (realizedProductCurrentEquiv realization 1).injective
    calc
      realizedProductCurrentEquiv realization 1
          (factorBoundary Product 1
            (realizedProductH1 realization datumX datumY current)) =
        diagonalBoundaryTwo X Y
          (realizedProductCurrentEquiv realization 2
            (realizedProductH1 realization datumX datumY current)) :=
        realizedProductCurrentEquiv_boundary_two realization _
      _ = diagonalBoundaryTwo X Y
          (productH1Diagonal datumX datumY
            (realizedProductCurrentEquiv realization 1 current)) := by
        apply congrArg (diagonalBoundaryTwo X Y)
        simp only [realizedProductH1, LinearMap.comp_apply]
        exact (realizedProductCurrentEquiv realization 2).apply_symm_apply _
      _ = realizedProductCurrentEquiv realization 1 current := by
        apply diagonalBoundaryTwo_productH1Diagonal_of_closed
        rw [← realizedProductCurrentEquiv_boundary_one, closed, map_zero]

section Audit

#print axioms diagonalBoundaryOne_productH0Diagonal
#print axioms totalBoundaryTwo_productTotalOneFilling
#print axioms diagonalBoundaryTwo_productH1Diagonal_of_closed
#print axioms productFirstFactorDegreeTwoCurrent_closed
#print axioms productSecondFactorDegreeTwoCurrent_closed
#print axioms leftOuterNormalizationCorrection_boundary
#print axioms rightOuterNormalizationCorrection_boundary
#print axioms productDegreeTwoNormalizationFiller_boundary
#print axioms coupledMiddleCorrection_reduces_to_outer
#print axioms totalBoundaryOne_totalBoundaryTwo
#print axioms diagonalBoundaryOne_diagonalBoundaryTwo
#print axioms realizedProductCurrentEquiv_boundary_one
#print axioms realizedProductCurrentEquiv_boundary_two
#print axioms realizedProductCurrentEquiv_boundary_three
#print axioms realizedProductFirstFactorDegreeTwoCurrent_closed
#print axioms realizedProductSecondFactorDegreeTwoCurrent_closed
#print axioms realizedProductDegreeTwoNormalizationFiller_boundary
#print axioms productAugmentation_diagonalBoundaryOne
#print axioms realizedProductLowDegreeCurrentDatum

end Audit

end Soma.Holonics.DiagonalChainTransport
