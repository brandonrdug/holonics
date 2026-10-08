import HolonicsResearch.Foundation.ProductAxisBoundary

/-!
# Product augmentation and endpoint return

The two factor augmentations, base-current receivers, and complete degree-zero contraction. The edge contraction consumes their exact endpoint returns.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

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

section Audit

#print axioms pairFirstAugmentation_generator
#print axioms pairFirstBase_generator
#print axioms pairFirstAugmentation_pairCurrent
#print axioms pairFirstBase_current
#print axioms productAugmentation_generator
#print axioms totalBoundaryOne_productH0SeparatedAtom
#print axioms totalBoundaryOne_productH0Separated
#print axioms diagonalBoundaryOne_productH0Diagonal
#print axioms pairSecondAugmentation_generator
#print axioms pairSecondBase_generator
#print axioms pairSecondAugmentation_pairCurrent
#print axioms pairSecondBase_current
#print axioms pairSecondAugmentation_mapPairLeft
#print axioms pairSecondAugmentation_mapPairRight_boundary
#print axioms mapPairRight_h0_boundary
#print axioms mapPairLeft_pairSecondBase

end Audit

end Holonics.DiagonalChainTransport
