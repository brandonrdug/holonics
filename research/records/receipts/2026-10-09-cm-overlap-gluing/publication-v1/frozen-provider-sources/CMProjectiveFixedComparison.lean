import CMProjectiveFixedPullback
import CMComplexGraph

/-! The narrow graph constructor is exactly the earlier actual closed graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem cmConcreteBase_eq : cmConcreteCubicBase = cmCubicBase := rfl
theorem cmConcreteGraph_eq : cmConcreteComplexGraph = cmComplexGraph := by
  rfl

def cmFixedActualGraphIso : CMProjectiveFixedScheme ≅
    pullback cmComplexGraph (pullback.diagonal cmCubicBase) :=
  pullback.congrHom cmConcreteGraph_eq rfl

theorem cmConcreteGraph_closedImmersion : IsClosedImmersion cmConcreteComplexGraph := by
  rw [cmConcreteGraph_eq]
  exact cmComplexGraph_closedImmersion

theorem cmFixedInclusion_closedImmersion : IsClosedImmersion cmFixedInclusion := by
  have : IsClosedImmersion cmComplexDiagonal := by
    unfold cmComplexDiagonal
    infer_instance
  unfold cmFixedInclusion
  exact MorphismProperty.pullback_fst (P := @IsClosedImmersion)
    cmConcreteComplexGraph cmComplexDiagonal ‹IsClosedImmersion cmComplexDiagonal›

#print axioms cmConcreteGraph_eq
#print axioms cmFixedActualGraphIso
#print axioms cmFixedInclusion_closedImmersion
end Holonics.Hodge.CMGraphSource
