import CMActualFixedIntrinsicLength
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! The actual structure morphism of the graph--diagonal pullback is kept.
Its two point maps are over Spec C by the actual chart-over-C squares and
the declared C-algebra origin receivers. Hence its residue field maps are
isomorphisms and its residue degrees are one. An abstract ring isomorphism
of an intrinsic stalk with C is not used to infer these structure maps.

agent-inferred: the base-map square is the required operand for a weighted
degree. The external helical pair receiver touches faces and placement,
cell holonomy and tube; helix, pair and tower remain attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

def cmActualFixedBase : CMProjectiveFixedScheme ⟶ cmComplexPoint :=
  cmFixedInclusion ≫ cmConcreteCubicBase

theorem cmActualYFixedPoint_over_complex :
    yActualFixedPoint ≫ cmActualFixedBase = 𝟙 cmComplexPoint := by
  rw [cmActualFixedBase, ← Category.assoc, cmActualYFixedPoint_inclusion_map,
    Category.assoc, yCurveChart_complex_base]
  change Spec.map (CommRingCat.ofHom yOriginReceiver.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ YChartCubicRing)) = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ YChartCubicRing) ≫
      CommRingCat.ofHom yOriginReceiver.toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact yOriginReceiver.commutes c
  rw [h, Spec.map_id]

theorem cmActualZFixedPoint_over_complex :
    zActualFixedPoint ≫ cmActualFixedBase = 𝟙 cmComplexPoint := by
  rw [cmActualFixedBase, ← Category.assoc, cmActualZFixedPoint_inclusion_map,
    Category.assoc, zCurveChart_complex_base]
  change Spec.map (CommRingCat.ofHom zOriginReceiver.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ CurveRing)) = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ CurveRing) ≫
      CommRingCat.ofHom zOriginReceiver.toRingHom = 𝟙 (CommRingCat.of ℂ) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact zOriginReceiver.commutes c
  rw [h, Spec.map_id]

/-- Retraction on schemes transports the residue map through the actual
point equality. The residue-field congruence keeps its changing source field. -/
theorem residueFieldMap_isIso_at_retraction {X Y : Scheme}
    (u : X ⟶ Y) (v : Y ⟶ X) [IsOpenImmersion u]
    (h : u ≫ v = 𝟙 X) (x : X) : IsIso (v.residueFieldMap (u x)) := by
  have : IsIso (v.residueFieldMap (u x) ≫ u.residueFieldMap x) := by
    rw [← Scheme.residueFieldMap_comp,
      Scheme.Hom.residueFieldMap_congr h x]
    infer_instance
  exact IsIso.of_isIso_comp_right (v.residueFieldMap (u x)) (u.residueFieldMap x)

/-- Keep exactly the residue map's algebra, which also defines residueDegree. -/
theorem residueDegree_one_of_residue_iso {X Y : Scheme} (f : X ⟶ Y) (x : X)
    [IsIso (f.residueFieldMap x)] : f.residueDegree x = 1 := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  apply Module.finrank_of_bijective_algebraMap
  change Function.Bijective (f.residueFieldMap x).hom
  exact (asIso (f.residueFieldMap x)).commRingCatIsoToRingEquiv.bijective

theorem cmActualYFixedBase_residueMap_isIso :
    IsIso (cmActualFixedBase.residueFieldMap cmActualYFixedPoint) :=
  residueFieldMap_isIso_at_retraction yActualFixedPoint cmActualFixedBase
    cmActualYFixedPoint_over_complex (IsLocalRing.closedPoint ℂ)

theorem cmActualZFixedBase_residueMap_isIso :
    IsIso (cmActualFixedBase.residueFieldMap cmActualZFixedPoint) :=
  residueFieldMap_isIso_at_retraction zActualFixedPoint cmActualFixedBase
    cmActualZFixedPoint_over_complex (IsLocalRing.closedPoint ℂ)

theorem cmActualYFixedResidueDegreeOne :
    cmActualFixedBase.residueDegree cmActualYFixedPoint = 1 := by
  have := cmActualYFixedBase_residueMap_isIso
  exact residueDegree_one_of_residue_iso cmActualFixedBase cmActualYFixedPoint

theorem cmActualZFixedResidueDegreeOne :
    cmActualFixedBase.residueDegree cmActualZFixedPoint = 1 := by
  have := cmActualZFixedBase_residueMap_isIso
  exact residueDegree_one_of_residue_iso cmActualFixedBase cmActualZFixedPoint

theorem cmActualFixedResidueDegreeOne (q : CMProjectiveFixedScheme) :
    cmActualFixedBase.residueDegree q = 1 := by
  rcases actualFixed_two_point_population q with h | h
  · rw [h]
    exact cmActualYFixedResidueDegreeOne
  · rw [h]
    exact cmActualZFixedResidueDegreeOne

#print axioms residueFieldMap_isIso_at_retraction
#print axioms residueDegree_one_of_residue_iso
#print axioms cmActualYFixedPoint_over_complex
#print axioms cmActualZFixedPoint_over_complex
#print axioms cmActualYFixedBase_residueMap_isIso
#print axioms cmActualZFixedBase_residueMap_isIso
#print axioms cmActualFixedResidueDegreeOne
end Holonics.Hodge.CMGraphSource
