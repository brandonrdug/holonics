import CMYAmbientProduct
import CMGraphChartPullback
import CMProjectiveFixedComparison
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! Genuine restrictions of the actual graph/diagonal ideal sheaves on
E x_C E to its actual Y x_C Y tensor spectrum. Further restrictions commute
through the existing ideal-sheaf pullback, rather than an assumed chart ideal. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Holonics.Hodge.CMGraphSource

theorem yTensorGraph_isPullback : IsPullback yTensorGraph yCurveChartInclusion
    yProductChartInclusion cmConcreteComplexGraph :=
  graphChart_isPullback yCurveChartInclusion yProductChartInclusion
    (Spec.map (CommRingCat.ofHom yLeft.toRingHom))
    (pullback.fst cmConcreteCubicBase cmConcreteCubicBase)
    yTensorGraph cmConcreteComplexGraph cmConcreteComplexGraph_first_projection
    yProductChart_first_projection yTensorGraph_actual_square

theorem yTensorDiagonal_isPullback : IsPullback yTensorDiagonal yCurveChartInclusion
    yProductChartInclusion cmComplexDiagonal :=
  graphChart_isPullback yCurveChartInclusion yProductChartInclusion
    (Spec.map (CommRingCat.ofHom yLeft.toRingHom))
    (pullback.fst cmConcreteCubicBase cmConcreteCubicBase)
    yTensorDiagonal cmComplexDiagonal
    (by simp [cmComplexDiagonal]) yProductChart_first_projection yTensorDiagonal_actual_square

theorem yTensorGraph_actual_ideal :
    cmConcreteComplexGraph.ker.comap yProductChartInclusion = yTensorGraph.ker := by
  letI : IsClosedImmersion cmConcreteComplexGraph := cmConcreteGraph_closedImmersion
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← yTensorGraph_isPullback.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

theorem yTensorDiagonal_actual_ideal :
    cmComplexDiagonal.ker.comap yProductChartInclusion = yTensorDiagonal.ker := by
  letI : IsClosedImmersion cmComplexDiagonal := by
    dsimp only [cmComplexDiagonal]
    infer_instance
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← yTensorDiagonal_isPullback.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

theorem yTensorGraph_ideal_restriction {U : Scheme} (r : U ⟶ Spec (.of YProductRing)) :
    cmConcreteComplexGraph.ker.comap (r ≫ yProductChartInclusion) =
      yTensorGraph.ker.comap r := by
  rw [Scheme.IdealSheafData.comap_comp, yTensorGraph_actual_ideal]

theorem yTensorDiagonal_ideal_restriction {U : Scheme} (r : U ⟶ Spec (.of YProductRing)) :
    cmComplexDiagonal.ker.comap (r ≫ yProductChartInclusion) =
      yTensorDiagonal.ker.comap r := by
  rw [Scheme.IdealSheafData.comap_comp, yTensorDiagonal_actual_ideal]

theorem yTensorGraph_support :
    yTensorGraph.ker.support = cmConcreteComplexGraph.ker.support.preimage
      yProductChartInclusion.continuous := by
  rw [← yTensorGraph_actual_ideal, Scheme.IdealSheafData.support_comap]

theorem yTensorDiagonal_support :
    yTensorDiagonal.ker.support = cmComplexDiagonal.ker.support.preimage
      yProductChartInclusion.continuous := by
  rw [← yTensorDiagonal_actual_ideal, Scheme.IdealSheafData.support_comap]

#print axioms yTensorGraph_isPullback
#print axioms yTensorDiagonal_isPullback
#print axioms yTensorGraph_actual_ideal
#print axioms yTensorDiagonal_actual_ideal
#print axioms yTensorGraph_ideal_restriction
#print axioms yTensorDiagonal_ideal_restriction
#print axioms yTensorGraph_support
#print axioms yTensorDiagonal_support
end Holonics.Hodge.CMGraphSource
