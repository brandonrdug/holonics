import HolonicsResearch.Foundation.ProductAugmentation

/-!
# Product edge contraction

The complete degree-one product filling, its diagonal consumer, and factor-boundary nilpotence returns. Degree-two normalization consumes this contraction.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

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

section Audit

#print axioms productOneBaseResidual_closed
#print axioms totalBoundaryTwo_productTotalOneFilling
#print axioms diagonalBoundaryTwo_productH1Diagonal_of_closed
#print axioms pairFirstAugmentation_mapPairRight
#print axioms pairFirstAugmentation_mapPairLeft_boundary
#print axioms mapPairLeft_h0_boundary
#print axioms mapPairLeft_factorBoundary_sq
#print axioms mapPairRight_factorBoundary_sq

end Audit

end Holonics.DiagonalChainTransport
