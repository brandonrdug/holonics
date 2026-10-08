import HolonicsResearch.Foundation.ProductEdgeContraction

/-!
# Product degree-two normalization

The coupled middle correction, separately closed outer returns, complete outer normalization, boundary nilpotence, and polarized filling. The actual product realization consumes these equations.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

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

section Audit

#print axioms coupledRightMiddleContraction_boundary
#print axioms coupledLeftMiddleCorrection_boundary
#print axioms coupledMiddleCorrection_boundary
#print axioms mixedFirstBoundary_closed_of_totalBoundary
#print axioms mixedSecondBoundary_closed_of_totalBoundary
#print axioms correctedFirstOuter_closed
#print axioms correctedSecondOuter_closed
#print axioms coupledMiddleCorrection_reduces_to_outer
#print axioms productFirstFactorDegreeTwoCurrent_closed
#print axioms productSecondFactorDegreeTwoCurrent_closed
#print axioms leftOuterNormalizationCorrection_boundary
#print axioms rightOuterNormalizationCorrection_boundary
#print axioms productDegreeTwoNormalizationFiller_boundary
#print axioms totalBoundaryOne_totalBoundaryTwo
#print axioms diagonalBoundaryOne_diagonalBoundaryTwo
#print axioms boundary_middlePolarizedFilling
#print axioms boundary_middlePolarizedFillingCurrent

end Audit

end Holonics.DiagonalChainTransport
