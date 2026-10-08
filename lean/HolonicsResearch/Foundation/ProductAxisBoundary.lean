import HolonicsResearch.Foundation.ProductFactorCurrent

/-!
# Product axis boundary receivers

The separated axes, their signed boundary returns, complete-current polarized filling, and coupled closure equations. Product augmentation consumes these receivers.

[agent-inferred] Declarations moved once from ProductDegreeTwo along their
existing mathematical dependency. Their bodies, names and hypotheses are
unchanged; checked predecessor objects are reusable by the next consumer.
-/

noncomputable section

namespace Holonics.DiagonalChainTransport

open CategoryTheory
open Simplicial

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

/-! [agent-inferred] Extend each proved generator boundary law once to the
complete current. Its reading on a polarized pair then follows by applying that
same axis law to `pairCurrent`. This removes the two nested factor-current
inductions and their repeated module normalization without changing any source
population, boundary law, or closure hypothesis. -/

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
      rw [totalBoundaryThree_rightMiddle_generator]
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
      rw [totalBoundaryThree_leftMiddle_generator]
      module

theorem totalBoundaryThree_rightMiddle {X Y : SSet}
    (left : FactorCurrent X 2) (right : FactorCurrent Y 1) :
    totalBoundaryThree X Y (rightMiddleAxis (pairCurrent left right)) =
      middleAxis (pairCurrent (factorBoundary X 1 left) right) +
        rightAxis (pairCurrent left (factorBoundary Y 0 right)) := by
  simpa only [mapPairLeft_pairCurrent, mapPairRight_pairCurrent] using
    totalBoundaryThree_rightMiddleAxis (pairCurrent left right)

theorem totalBoundaryThree_leftMiddle {X Y : SSet}
    (left : FactorCurrent X 1) (right : FactorCurrent Y 2) :
    totalBoundaryThree X Y (leftMiddleAxis (pairCurrent left right)) =
      leftAxis (pairCurrent (factorBoundary X 0 left) right) -
        middleAxis (pairCurrent left (factorBoundary Y 1 right)) := by
  simpa only [mapPairLeft_pairCurrent, mapPairRight_pairCurrent] using
    totalBoundaryThree_leftMiddleAxis (pairCurrent left right)

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

/-! [agent-inferred] The axis boundary laws are equalities of linear receivers.
Compose each occurrence receiver before extending it, using the existing
`linearCombination_linear_comp` law; only the signed generator equation is
calculated. The mixed return is extended by `Finsupp.lhom_ext`. This avoids
normalizing an arbitrary coefficient inside each boundary calculation while
retaining every occurrence and every coupled-axis return. -/

theorem totalBoundaryOne_leftOneAxis {X Y : SSet}
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 1)) :
    totalBoundaryOne X Y (leftOneAxis current) =
      mapPairRight (factorBoundary Y 0) current := by
  have mapLaw : (totalBoundaryOne X Y).comp leftOneAxis =
      mapPairRight (factorBoundary Y 0) := by
    change (totalBoundaryOne X Y).comp (Finsupp.linearCombination ℚ _) =
      Finsupp.linearCombination ℚ _
    rw [← Finsupp.linearCombination_linear_comp]
    apply congrArg (Finsupp.linearCombination ℚ)
    funext pair
    rcases pair with ⟨left, right⟩
    simp only [Function.comp_apply, totalBoundaryOne, extend_generator,
      totalBoundaryOneAtom, factorBoundary_generator, factorBoundaryAtom]
    rw [Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  exact LinearMap.congr_fun mapLaw current

theorem totalBoundaryOne_rightOneAxis {X Y : SSet}
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 0)) :
    totalBoundaryOne X Y (rightOneAxis current) =
      mapPairLeft (factorBoundary X 0) current := by
  have mapLaw : (totalBoundaryOne X Y).comp rightOneAxis =
      mapPairLeft (factorBoundary X 0) := by
    change (totalBoundaryOne X Y).comp (Finsupp.linearCombination ℚ _) =
      Finsupp.linearCombination ℚ _
    rw [← Finsupp.linearCombination_linear_comp]
    apply congrArg (Finsupp.linearCombination ℚ)
    funext pair
    rcases pair with ⟨left, right⟩
    simp only [Function.comp_apply, totalBoundaryOne, extend_generator,
      totalBoundaryOneAtom, factorBoundary_generator, factorBoundaryAtom]
    rw [Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  exact LinearMap.congr_fun mapLaw current

theorem totalBoundaryTwo_leftAxis {X Y : SSet}
    (current : Current (FactorSimplex X 0 × FactorSimplex Y 2)) :
    totalBoundaryTwo X Y (leftAxis current) =
      leftOneAxis (mapPairRight (factorBoundary Y 1) current) := by
  have mapLaw : (totalBoundaryTwo X Y).comp leftAxis =
      leftOneAxis.comp (mapPairRight (factorBoundary Y 1)) := by
    change (totalBoundaryTwo X Y).comp (Finsupp.linearCombination ℚ _) =
      leftOneAxis.comp (Finsupp.linearCombination ℚ _)
    rw [← Finsupp.linearCombination_linear_comp,
      ← Finsupp.linearCombination_linear_comp]
    apply congrArg (Finsupp.linearCombination ℚ)
    funext pair
    rcases pair with ⟨left, right⟩
    simp only [Function.comp_apply, totalBoundaryTwo, extend_generator,
      totalBoundaryTwoAtom, factorBoundary_generator, factorBoundaryAtom]
    rw [Fin.sum_univ_three]
    simp [sub_eq_add_neg]
  exact LinearMap.congr_fun mapLaw current

theorem totalBoundaryTwo_middleAxis {X Y : SSet}
    (current : Current (FactorSimplex X 1 × FactorSimplex Y 1)) :
    totalBoundaryTwo X Y (middleAxis current) =
      leftOneAxis (mapPairLeft (factorBoundary X 0) current) -
        rightOneAxis (mapPairRight (factorBoundary Y 0) current) := by
  have generatorLaw : ∀ pair : FactorSimplex X 1 × FactorSimplex Y 1,
      totalBoundaryTwo X Y (middleAxis (generator pair)) =
        leftOneAxis (mapPairLeft (factorBoundary X 0) (generator pair)) -
          rightOneAxis (mapPairRight (factorBoundary Y 0) (generator pair)) := by
    rintro ⟨left, right⟩
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
    simp only [middleAxis_generator, totalBoundaryTwo, extend_generator,
      totalBoundaryTwoAtom, leftLaw, rightLaw, map_sub,
      leftOneAxis_generator, rightOneAxis_generator]
    abel
  have mapLaw : (totalBoundaryTwo X Y).comp middleAxis =
      leftOneAxis.comp (mapPairLeft (factorBoundary X 0)) -
        rightOneAxis.comp (mapPairRight (factorBoundary Y 0)) := by
    apply Finsupp.lhom_ext
    intro pair coefficient
    rw [show Finsupp.single pair coefficient =
        coefficient • generator pair by simp [generator]]
    simpa only [LinearMap.comp_apply, LinearMap.sub_apply, map_smul, smul_sub]
      using congrArg (coefficient • ·) (generatorLaw pair)
  exact LinearMap.congr_fun mapLaw current

theorem totalBoundaryTwo_rightAxis {X Y : SSet}
    (current : Current (FactorSimplex X 2 × FactorSimplex Y 0)) :
    totalBoundaryTwo X Y (rightAxis current) =
      rightOneAxis (mapPairLeft (factorBoundary X 1) current) := by
  have mapLaw : (totalBoundaryTwo X Y).comp rightAxis =
      rightOneAxis.comp (mapPairLeft (factorBoundary X 1)) := by
    change (totalBoundaryTwo X Y).comp (Finsupp.linearCombination ℚ _) =
      rightOneAxis.comp (Finsupp.linearCombination ℚ _)
    rw [← Finsupp.linearCombination_linear_comp,
      ← Finsupp.linearCombination_linear_comp]
    apply congrArg (Finsupp.linearCombination ℚ)
    funext pair
    rcases pair with ⟨left, right⟩
    simp only [Function.comp_apply, totalBoundaryTwo, extend_generator,
      totalBoundaryTwoAtom, factorBoundary_generator, factorBoundaryAtom]
    rw [Fin.sum_univ_three]
    simp [sub_eq_add_neg]
  exact LinearMap.congr_fun mapLaw current

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

section Audit

#print axioms leftAxis_generator
#print axioms middleAxis_generator
#print axioms rightAxis_generator
#print axioms leftMiddleAxis_generator
#print axioms rightMiddleAxis_generator
#print axioms totalBoundaryThree_rightMiddle_generator
#print axioms totalBoundaryThree_leftMiddle_generator
#print axioms totalBoundaryThree_rightMiddleAxis
#print axioms totalBoundaryThree_leftMiddleAxis
#print axioms totalBoundaryThree_rightMiddle
#print axioms totalBoundaryThree_leftMiddle
#print axioms mapPairLeft_extendedH1_boundary
#print axioms mapPairRight_extendedH1_boundary
#print axioms boundary_middleJointFillingLeft
#print axioms boundary_middleJointFillingRight
#print axioms leftOneAxis_generator
#print axioms rightOneAxis_generator
#print axioms totalBoundaryOne_leftOneAxis
#print axioms totalBoundaryOne_rightOneAxis
#print axioms totalBoundaryTwo_leftAxis
#print axioms totalBoundaryTwo_middleAxis
#print axioms totalBoundaryTwo_rightAxis
#print axioms totalOneAxisReconstruction
#print axioms totalBoundaryOne_axisDecomposition
#print axioms leftAxisProjection_generator
#print axioms middleAxisProjection_generator
#print axioms rightAxisProjection_generator
#print axioms leftOneAxisProjection_generator
#print axioms rightOneAxisProjection_generator
#print axioms totalTwoAxisReconstruction
#print axioms leftOneAxisProjection_totalBoundaryTwo
#print axioms rightOneAxisProjection_totalBoundaryTwo
#print axioms coupledAxisBoundaryEquations

end Audit

end Holonics.DiagonalChainTransport
