import ElementaryHolonics.Millennium.HodgeTriangleHomotopyPrism

/-!
# Familywise cancellation of affine-label edge corrections

The raw affine label target keeps ordered words, including repeated and non-monotone words.  Its
degree-one correction is therefore an addressed current, not an endpoint sign convention.  This
file lifts that current to the complete refined-cell population: a receiver on a singular edge
chooses a represented refined face, representative independence is proved from the actual source
map, and the resulting linear receiver factors the coefficient-weighted side current through the
ordinary refined boundary.

Truth status: definitions are `[definition]`; the cancellation laws are
`[proved-derived; formal-checked]` relative to the exact raw correction law and the exact refined
boundary law imported from `HodgeTriangleHomotopyPrism`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeLabelEdgeCancellation

open CategoryTheory Set Topology
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeRefinementWords
open Soma.Holonics.Millennium.HodgeIteratedBarycentricHomology
open Soma.Holonics.Millennium.HodgeBarycentricTriangleSubdivision
open Soma.Holonics.Millennium.HodgeBarycentricTetrahedron
open Soma.Holonics.Millennium.HodgeRadialCurrent
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralLabelCarry
open Soma.Holonics.Millennium.HodgeFiniteClosedStarLabeling
open Soma.Holonics.Millennium.HodgeRefinedTriangleClosedStar
open Soma.Holonics.Millennium.HodgeRefinedTriangleAffineCarrier
open Soma.Holonics.Millennium.HodgeTriangleHomotopyPrism

abbrev SphereChain (degree : ℕ) := SphereSingularChainComplex.X degree

/-- The ordered two-label face word read from one addressed refined triangle-face occurrence. -/
def refinedFaceLabels {chain : SphereChain 2} {scale : ℕ}
    (lebesgue : StarLebesgueLabel)
    (labeling : (refinedTriangleComplex chain scale).ClosedStarLabeling)
    (occurrence : RefinedTriangleFace (chain := chain) (scale := scale)) :
    Fin 2 → TetraVertex :=
  refinedCellLabels lebesgue labeling occurrence.1 ∘ occurrence.2.succAbove

/-- The raw degree-one correction attached to one exact addressed refined face. -/
def refinedFaceEdgeCorrection {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (occurrence : RefinedTriangleFace (chain := chain) (scale := family.scale)) :
    SphereChain 2 :=
  rawAffineLabelEdgeCorrection
    ((refinedFaceLabels lebesgue family.labeling occurrence) 0)
    ((refinedFaceLabels lebesgue family.labeling occurrence) 1)

/-- Equality of the complete correction current follows from equality of the retained ordered
label word. -/
theorem refinedFaceEdgeCorrection_congr
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (first second : RefinedTriangleFace
      (chain := chain) (scale := family.scale))
    (sourceLaw : refinedTriangleFaceSimplex first = refinedTriangleFaceSimplex second) :
    refinedFaceEdgeCorrection family first = refinedFaceEdgeCorrection family second := by
  have sourceLaw' :
      (refinedTriangleSourceMap first.1).comp
          (simplexFaceMap (degree := 1) first.2) =
        (refinedTriangleSourceMap second.1).comp
          (simplexFaceMap (degree := 1) second.2) := by
    change simplexFace first.2 (refinedTriangleSimplex first.1) =
      simplexFace second.2 (refinedTriangleSimplex second.1) at sourceLaw
    exact congrArg
      (TopCat.toSSetObjEquiv sphereTopCat
        (Opposite.op (SimplexCategory.mk 1))) sourceLaw
  have labelLaw := refinedCellLabels_face_congr
    lebesgue family.labeling first.1 second.1 first.2 second.2 sourceLaw'
  unfold refinedFaceEdgeCorrection refinedFaceLabels
  rw [labelLaw]

/-- An edge receiver returns the correction current of a represented refined face and zero on an
unrepresented singular edge.  The receiver's choice is lawful because the previous theorem
retains the complete label word, including repeats and orientation. -/
def refinedEdgeCorrection {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (simplex : SphereSingularSimplex 1) : SphereChain 2 := by
  classical
  if represented : ∃ occurrence : RefinedTriangleFace
      (chain := chain) (scale := family.scale),
      refinedTriangleFaceSimplex occurrence = simplex then
    let occurrence := Classical.choose represented
    exact refinedFaceEdgeCorrection family occurrence
  else
    exact 0

/-- Every represented edge evaluates to its addressed refined-face correction, independently of
the representative selected by the receiver. -/
theorem refinedEdgeCorrection_refinedFace
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (occurrence : RefinedTriangleFace
      (chain := chain) (scale := family.scale)) :
    refinedEdgeCorrection family (refinedTriangleFaceSimplex occurrence) =
      refinedFaceEdgeCorrection family occurrence := by
  classical
  rw [refinedEdgeCorrection]
  split_ifs with represented
  · let selected := Classical.choose represented
    have selectedLaw : refinedTriangleFaceSimplex selected =
        refinedTriangleFaceSimplex occurrence := Classical.choose_spec represented
    exact refinedFaceEdgeCorrection_congr family selected occurrence selectedLaw
  · exact False.elim (represented ⟨occurrence, rfl⟩)

/-- Rational coefficient transport into one correction current. -/
def refinedEdgeCorrectionCoefficient (value : SphereChain 2) :
    rationalCoefficient ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        simp only [RingHom.id_apply, smul_eq_mul, mul_smul]
        rfl }

/-- Coproduct-linear extension of the represented-edge correction receiver. -/
def refinedEdgeCorrectionMorphism {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    SphereSingularChainComplex.X 1 ⟶ SphereSingularChainComplex.X 2 :=
  Limits.Sigma.desc fun simplex =>
    refinedEdgeCorrectionCoefficient (refinedEdgeCorrection family simplex)

@[simp] theorem refinedEdgeCorrectionMorphism_simplexGenerator
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (simplex : SphereSingularSimplex 1) :
    refinedEdgeCorrectionMorphism family (simplexGenerator simplex) =
      refinedEdgeCorrection family simplex := by
  change ((Limits.Sigma.ι
      (fun _ : SphereSingularSimplex 1 => rationalCoefficient) simplex ≫
        Limits.Sigma.desc (fun source => refinedEdgeCorrectionCoefficient
          (refinedEdgeCorrection family source))) (1 : ℚ)) = _
  rw [Limits.Sigma.ι_desc]
  exact one_smul ℚ _

/-- The coefficient-weighted alternating correction side current of the complete refined-cell
population.  The three terms are the actual oriented faces of every refined triangle. -/
def refinedFaceEdgeCorrectionCurrent {chain : SphereChain 2}
    {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) : SphereChain 2 :=
  ∑ cell : RefinedTriangleCell chain family.scale,
    refinedTriangleCoefficient cell •
      (refinedFaceEdgeCorrection family (cell, (0 : Fin 3)) -
        refinedFaceEdgeCorrection family (cell, (1 : Fin 3)) +
          refinedFaceEdgeCorrection family (cell, (2 : Fin 3)))

/-- The local three-face correction is exactly the correction receiver applied to the ordinary
boundary of the refined singular triangle. -/
theorem refinedFaceEdgeCorrection_local_boundary
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cell : RefinedTriangleCell chain family.scale) :
    refinedFaceEdgeCorrection family (cell, (0 : Fin 3)) -
        refinedFaceEdgeCorrection family (cell, (1 : Fin 3)) +
          refinedFaceEdgeCorrection family (cell, (2 : Fin 3)) =
      refinedEdgeCorrectionMorphism family
        (SphereSingularChainComplex.d 2 1
          (simplexGenerator (refinedTriangleSimplex cell))) := by
  rw [boundary_simplexGenerator, Fin.sum_univ_three]
  simp only [map_sub, map_add, map_smul,
    refinedEdgeCorrectionMorphism_simplexGenerator]
  have hface (face : Fin 3) :
      refinedEdgeCorrection family
          (simplexFace face (refinedTriangleSimplex cell)) =
        refinedFaceEdgeCorrection family (cell, face) := by
    rw [← refinedEdgeCorrection_refinedFace family (cell, face)]
    rfl
  rw [hface 0, hface 1, hface 2]
  norm_num
  abel

/-- The full coefficient-weighted side current factors through the ordinary boundary of the
iterated barycentric refinement. -/
theorem refinedFaceEdgeCorrectionCurrent_eq_boundary
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue) :
    refinedFaceEdgeCorrectionCurrent family =
      refinedEdgeCorrectionMorphism family
        (SphereSingularChainComplex.d 2 1
          (iteratedBarycentricTriangleSubdivision family.scale chain)) := by
  rw [refinedFaceEdgeCorrectionCurrent,
    ← sum_refinedTriangleCoefficient_simplexGenerator chain family.scale]
  simp only [map_sum, map_smul]
  apply Fintype.sum_congr
  intro cell
  rw [refinedFaceEdgeCorrection_local_boundary]

/-- A source two-cycle has zero familywise affine-label correction side current. -/
theorem refinedFaceEdgeCorrectionCurrent_eq_zero
    {chain : SphereChain 2} {lebesgue : StarLebesgueLabel}
    (family : RefinedAffineCarrierFamily chain lebesgue)
    (cycle : SphereSingularChainComplex.d 2 1 chain = 0) :
    refinedFaceEdgeCorrectionCurrent family = 0 := by
  rw [refinedFaceEdgeCorrectionCurrent_eq_boundary,
    boundary_iteratedBarycentricTriangleSubdivision, cycle,
    iteratedBarycentricEdgeSubdivision_zero, map_zero]

#print axioms refinedFaceEdgeCorrection_congr
#print axioms refinedEdgeCorrection_refinedFace
#print axioms refinedFaceEdgeCorrectionCurrent_eq_boundary
#print axioms refinedFaceEdgeCorrectionCurrent_eq_zero

end Soma.Holonics.Millennium.HodgeLabelEdgeCancellation
